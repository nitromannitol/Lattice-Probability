/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1B2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAShell

/-!
DG (`metric-comparison-final.tex`, Lemma 3.1 `lem-gff-compare`, DG:966–974; proof DG:2243–2244
"Combine Lemmas 2.2, A.1 and A.2"), circle-average reading D100, all fields from one white noise
`W` ("`ĥ` and `ĥ^tr` are defined using the same white noise", DG:974):

* `DGCircMod P S F`: there is a continuous measurable process `Y` with the Gaussian tail (3.5) on
  `S` whose circle averages over every circle `∂B(z,r)` with `B̄(z,r) ⊆ S` are a.s. `F z r`
  (the circle averages of `h¹ − h²`). Closed under differences (`DGCircMod.sub`): this is
  DG's "combine".
* **`dg_lemma31_hU_tr_circ`** — the pair `(h^U, ĥ^tr)` (DG Lemma A.1 `dg_lemmaA1_wn`, stochastic
  Fubini `ae_integral_eq_wn`, the kernel identity `integral_dgA1Kernel_ae_eq`);
* **`dg_lemma31_hU_hat_circ'`** — the pair `(h^U, ĥ)` (`dg_lemma31_hU_hat_circ`) in this form;
* **`dg_lemma31_hat_tr_circ`** — the pair `(ĥ, ĥ^tr)`, as `(h^U − ĥ^tr) − (h^U − ĥ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DG Lemma 3.1's conclusion for one pair, circle-average form (D100): a continuous modification
`Y` of `(h¹ − h²)|_S` (circle averages of `h¹ − h²` given by `F z r`) with the tail (3.5). -/
def DGCircMod (P : Measure Ω) (S : Set ℂ) (F : ℂ → ℝ → Ω → ℝ) : Prop :=
  ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
    (∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ S, |Y z ω| ≤ A} ≤ ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2))) ∧
    ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ S →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] F z r

lemma integrable_circleUnif_of_continuous {f : ℂ → ℝ} (hf : Continuous f) {z : ℂ} {r : ℝ}
    (hr : 0 < r) : Integrable f (circleUnif z r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hf.continuousOn
  have hae : ∀ᵐ x ∂(circleUnif z r), x ∈ Metric.closedBall z r :=
    mem_ae_iff.2 (circleUnif_compl_closedBall hr z)
  exact Integrable.of_bound hf.aestronglyMeasurable M (hae.mono fun x hx => hM x hx)

/-- union bound for two Gaussian tails -/
lemma tail_sub_le {S : Set ℂ} {Y₁ Y₂ : ℂ → Ω → ℝ} {a₀ a₁ b₀ b₁ : ℝ} (ha : 0 < a₁) (hb : 0 < b₁)
    (h₁ : ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ S, |Y₁ z ω| ≤ A} ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ * A ^ 2)))
    (h₂ : ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ S, |Y₂ z ω| ≤ A} ≤ ENNReal.ofReal (b₀ * Real.exp (-b₁ * A ^ 2))) :
    ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | ¬ ∀ z ∈ S, |Y₁ z ω - Y₂ z ω| ≤ A} ≤
        ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  refine ⟨|a₀| + |b₀|, min a₁ b₁ / 4, by positivity, fun A hA => ?_⟩
  have hsub : {ω | ¬ ∀ z ∈ S, |Y₁ z ω - Y₂ z ω| ≤ A} ⊆
      {ω | ¬ ∀ z ∈ S, |Y₁ z ω| ≤ A / 2} ∪ {ω | ¬ ∀ z ∈ S, |Y₂ z ω| ≤ A / 2} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hω hc
    exact hω fun z hz => (abs_sub _ _).trans (by linarith [hc.1 z hz, hc.2 z hz])
  have hA2 : 0 ≤ A / 2 := by linarith
  have e1 : Real.exp (-a₁ * (A / 2) ^ 2) ≤ Real.exp (-(min a₁ b₁ / 4) * A ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left a₁ b₁, sq_nonneg A])
  have e2 : Real.exp (-b₁ * (A / 2) ^ 2) ≤ Real.exp (-(min a₁ b₁ / 4) * A ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right a₁ b₁, sq_nonneg A])
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (h₁ _ hA2) (h₂ _ hA2)).trans ?_
  have p1 := Real.exp_pos (-a₁ * (A / 2) ^ 2)
  have p2 := Real.exp_pos (-b₁ * (A / 2) ^ 2)
  have q1 : a₀ * Real.exp (-a₁ * (A / 2) ^ 2) ≤ |a₀| * Real.exp (-(min a₁ b₁ / 4) * A ^ 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self a₀) p1.le).trans
      (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
  have q2 : b₀ * Real.exp (-b₁ * (A / 2) ^ 2) ≤ |b₀| * Real.exp (-(min a₁ b₁ / 4) * A ^ 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self b₀) p2.le).trans
      (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
  refine (add_le_add (ENNReal.ofReal_le_ofReal q1) (ENNReal.ofReal_le_ofReal q2)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- DG's "combine": the difference of two pairs -/
theorem DGCircMod.sub {S : Set ℂ} {F G : ℂ → ℝ → Ω → ℝ} (hF : DGCircMod P S F)
    (hG : DGCircMod P S G) : DGCircMod P S fun z r ω => F z r ω - G z r ω := by
  obtain ⟨Y₁, hc₁, hm₁, ⟨a₀, a₁, ha, h₁⟩, hF⟩ := hF
  obtain ⟨Y₂, hc₂, hm₂, ⟨b₀, b₁, hb, h₂⟩, hG⟩ := hG
  refine ⟨fun z ω => Y₁ z ω - Y₂ z ω, fun ω => (hc₁ ω).sub (hc₂ ω), fun z => (hm₁ z).sub (hm₂ z),
    tail_sub_le ha hb h₁ h₂, fun z r hr hB => ?_⟩
  filter_upwards [hF z r hr hB, hG z r hr hB] with ω e1 e2
  rw [integral_sub (integrable_circleUnif_of_continuous (hc₁ ω) hr)
    (integrable_circleUnif_of_continuous (hc₂ ω) hr), e1, e2]

theorem DGCircMod.congr {S : Set ℂ} {F G : ℂ → ℝ → Ω → ℝ} (hF : DGCircMod P S F)
    (h : ∀ z r ω, F z r ω = G z r ω) : DGCircMod P S G := by
  obtain ⟨Y, hc, hm, hT, hF⟩ := hF
  refine ⟨Y, hc, hm, hT, fun z r hr hB => ?_⟩
  filter_upwards [hF z r hr hB] with ω e
  rw [e, h]

/-- **DG Lemma 3.1 for `(h^U, ĥ)`, `U = 𝕍`**, as `DGCircMod` -/
theorem dg_lemma31_hU_hat_circ' (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    DGCircMod P (ferniqueBox y b) fun z r ω =>
      Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω -
        Real.sqrt Real.pi * W (hatMeasKerL2 (circleUnif z r)) ω :=
  dg_lemma31_hU_hat_circ hW hb hK

end DG
end LQGMetric
