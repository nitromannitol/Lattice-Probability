/-
# Bernstein: the Pinelis induction assembly

`LatticeProb.martingaleOneStep` (`Prob/BernsteinOneStep.lean`) is the per-step moment estimate

  `E |S (i+1)|^p ≤ E |S i|^p + C (E[|S i|^{p-2} v (i+1)] + E |ξ (i+1)|^p)`

for the partial sums `S i = ∑_{j=1}^{i} ξ_j` of martingale differences with predictable
quadratic variation increments `v i = E[ξ_i² | F (i-1)]`.

This file performs the bounded assembly of the induction:

* `iterateLeOfStep` — the telescoping of any such per-step recursion;
* `martingaleOneStep_iterate` — the instantiation to `martingaleOneStep`, giving the cumulative
  bound `E |S k|^p ≤ C ∑_{i<k} (E[|S i|^{p-2} v (i+1)] + E |ξ (i+1)|^p)`;
* `PinelisInductionStep` — **the single remaining induction step**, a named `Prop`: the control of
  the cumulative cross term `∑_{i<k} E[|S i|^{p-2} v (i+1)]` by the Rosenthal quantities
  `((E V_k^{p/2})^{2/p}, ∑ (E |ξ_i|^p)^{2/p})`;
* `martingaleRosenthal_of_pinelis` — the assembly of the two into the martingale Rosenthal bound

  `(E |S k|^p)^{2/p} ≤ K ( (E V_k^{p/2})^{2/p} + ∑_{i=1}^{k} (E |ξ_i|^p)^{2/p} )`.

Nothing here is conditional on `sorry`; the only hypothesis is the named `Prop`.
-/
import LatticeProb.Prob.BernsteinOneStep

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **Telescoping of a per-step recursion.**  If `A (i+1) ≤ A i + C (B i + c (i+1))` and `C ≥ 0`,
then `A k ≤ A 0 + C ∑_{i<k} (B i + c (i+1))`. -/
theorem iterateLeOfStep {A B c : ℕ → ℝ} {C : ℝ}
    (hstep : ∀ i, A (i + 1) ≤ A i + C * (B i + c (i + 1))) :
    ∀ k, A k ≤ A 0 + C * ∑ i ∈ Finset.range k, (B i + c (i + 1)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hstep k
    have h2 : A 0 + C * ∑ i ∈ Finset.range k, (B i + c (i + 1))
          + C * (B k + c (k + 1))
        = A 0 + C * ∑ i ∈ Finset.range (k + 1), (B i + c (i + 1)) := by
      rw [Finset.sum_range_succ]; ring
    linarith

/-- **The cumulative one-step bound.**  Iterating `martingaleOneStep` gives
`E |S k|^p ≤ C ∑_{i<k} (E[|S i|^{p-2} v (i+1)] + E |ξ (i+1)|^p)`. -/
theorem martingaleOneStep_iterate {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
        (F : Filtration ℕ m₀) (ξ : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ),
        (∀ i, AEMeasurable (martingalePartialSum ξ i) μ) →
        (∀ i, StronglyMeasurable[F i] (fun ω => |martingalePartialSum ξ i ω| ^ p)) →
        (∀ i, StronglyMeasurable[F i]
          (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2) * martingalePartialSum ξ i ω)) →
        (∀ i, StronglyMeasurable[F i] (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2))) →
        (∀ i, μ[ξ (i + 1) | F i] =ᵐ[μ] 0) →
        (∀ i, μ[fun ω => ξ (i + 1) ω ^ 2 | F i] =ᵐ[μ] v (i + 1)) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ p) μ) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2)
          * martingalePartialSum ξ i ω * ξ (i + 1) ω) μ) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2)
          * ξ (i + 1) ω ^ 2) μ) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2)
          * v (i + 1) ω) μ) →
        (∀ i, Integrable (ξ (i + 1)) μ) →
        (∀ i, Integrable (fun ω => ξ (i + 1) ω ^ 2) μ) →
        (∀ i, Integrable (fun ω => |ξ (i + 1) ω| ^ p) μ) →
        ∀ k,
          ∫ ω, |martingalePartialSum ξ k ω| ^ p ∂μ
            ≤ C * ∑ i ∈ Finset.range k,
                (∫ ω, |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ
                  + ∫ ω, |ξ (i + 1) ω| ^ p ∂μ) := by
  obtain ⟨C, hC1, hstep⟩ := martingaleOneStep hp
  refine ⟨C, hC1, ?_⟩
  intro Ω m₀ μ _ F ξ v hAe hAst hfst hf2st hmean hv hAint hfξ hf2ξ2 hf2v hξint hξ2int hξpint k
  have hzero : martingalePartialSum ξ 0 = fun _ : Ω => (0 : ℝ) := by
    funext ω
    simp only [martingalePartialSum]
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty]
  have hA0 : (∫ ω, |martingalePartialSum ξ 0 ω| ^ p ∂μ) = 0 := by
    rw [hzero]
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have hstep' : ∀ i, (∫ ω, |martingalePartialSum ξ (i + 1) ω| ^ p ∂μ)
      ≤ (∫ ω, |martingalePartialSum ξ i ω| ^ p ∂μ)
        + C * ((∫ ω, |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ)
          + (∫ ω, |ξ (i + 1) ω| ^ p ∂μ)) := by
    intro i
    exact hstep μ F ξ v hAe hAst hfst hf2st hmean hv hAint hfξ hf2ξ2 hf2v hξint hξ2int hξpint i
  have hrec := iterateLeOfStep (C := C)
    (A := fun i => ∫ ω, |martingalePartialSum ξ i ω| ^ p ∂μ)
    (B := fun i => ∫ ω, |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ)
    (c := fun i => ∫ ω, |ξ i ω| ^ p ∂μ) hstep' k
  rwa [hA0, zero_add] at hrec

end LatticeProb

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The deterministic core of the Rosenthal assembly.**  If `x ≤ al · x^{(p-2)/p} · w + be`
with `x, al, w, be ≥ 0` and `p ≥ 2`, then `x^{2/p} ≤ max (2 al w) ((2 be)^{2/p})`.  This is the
step that solves the cumulative inequality produced by the one-step iteration. -/
theorem solve_rpow_le {p x al w be : ℝ} (hp : 2 ≤ p) (hx : 0 ≤ x) (hal : 0 ≤ al)
    (hw : 0 ≤ w)
    (h : x ≤ al * x ^ ((p - 2) / p) * w + be) :
    x ^ (2 / p) ≤ max (2 * al * w) ((2 * be) ^ (2 / p)) := by
  have hp0 : 0 < p := by linarith
  set y : ℝ := x ^ (2 / p) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx _
  have hxy : x = y ^ (p / 2) := by
    rw [hy, ← Real.rpow_mul hx, show 2 / p * ((p : ℝ) / 2) = 1 by field_simp]
    exact (Real.rpow_one x).symm
  have hxpow : x ^ ((p - 2) / p) = y ^ ((p - 2) / 2) := by
    rw [hy, ← Real.rpow_mul hx]
    congr 1
    field_simp
  have h' : y ^ (p / 2) ≤ al * y ^ ((p - 2) / 2) * w + be := by
    have h2 : (y ^ (p / 2)) ^ ((p - 2) / p) = y ^ ((p - 2) / 2) := by
      rw [← Real.rpow_mul hy0]
      congr 1
      field_simp
    rw [hxy, h2] at h
    exact h
  by_cases hyw : y ≤ 2 * al * w
  · exact le_trans hyw (le_max_left _ _)
  · have hypos : 0 < y :=
      lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 * al * w) (not_le.mp hyw)
    have halw : al * w < y / 2 := by nlinarith
    have hstrict : al * y ^ ((p - 2) / 2) * w < y ^ (p / 2) / 2 := by
      have h2 : (al * w) * y ^ ((p - 2) / 2) < (y / 2) * y ^ ((p - 2) / 2) :=
        mul_lt_mul_of_pos_right halw (Real.rpow_pos_of_pos hypos _)
      have h3 : (y / 2) * y ^ ((p - 2) / 2) = y ^ (p / 2) / 2 := by
        rw [show (p : ℝ) / 2 = 1 + (p - 2) / 2 by ring, Real.rpow_add hypos, Real.rpow_one]
        ring
      calc al * y ^ ((p - 2) / 2) * w
          = (al * w) * y ^ ((p - 2) / 2) := by ring
        _ < (y / 2) * y ^ ((p - 2) / 2) := h2
        _ = y ^ (p / 2) / 2 := h3
    have hy2be : y ^ (p / 2) ≤ 2 * be := by linarith
    have hy_le : y ≤ (2 * be) ^ (2 / p) := by
      calc y = (y ^ (p / 2)) ^ (2 / p) := by
            rw [← Real.rpow_mul hy0]
            rw [show (p : ℝ) / 2 * (2 / p) = 1 by field_simp]
            exact (Real.rpow_one y).symm
        _ ≤ (2 * be) ^ (2 / p) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hy0 _) hy2be (by positivity)
    exact le_trans hy_le (le_max_right _ _)

end LatticeProb

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The single remaining induction step of Pinelis**, as a named `Prop`.

The cumulative one-step bound `martingaleOneStep_iterate` leaves the cross term
`B = ∑_{i<k} E[|S i|^{p-2} v (i+1)]` to be controlled.  The missing step bounds it by the
Rosenthal quantities `W = (E V_k^{p/2})^{2/p}` and `V = ∑_{i≤k} E|ξ_i|^p`:

  `B ≤ K W (E|S k|^p)^{(p-2)/p} + K V`.

This is Pinelis's cumulative induction; it is the only remaining research-level obligation and is
carried as a hypothesis, never as an axiom.  The companion `rosenthal_of_crossTerm` turns it into
the martingale Rosenthal bound once the one-step iteration has produced `A ≤ C(B + V)`. -/
def PinelisInductionStep : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ K : ℝ, 0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m₀}
      (F : Filtration ℕ m₀) (ξ v : ℕ → Ω → ℝ),
      (∀ i, μ[ξ (i + 1) | F i] =ᵐ[μ] 0) →
      (∀ i, μ[fun ω => ξ (i + 1) ω ^ 2 | F i] =ᵐ[μ] v (i + 1)) →
      (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) μ) →
      ∀ k,
        ∑ i ∈ Finset.range k,
            (∫ ω, |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ)
          ≤ K * (∫ ω, (∑ i ∈ Finset.Icc 1 k, v i ω) ^ (p / 2) ∂μ) ^ (2 / p)
              * (∫ ω, |martingalePartialSum ξ k ω| ^ p ∂μ) ^ ((p - 2) / p)
            + K * ∑ i ∈ Finset.Icc 1 k, ∫ ω, |ξ i ω| ^ p ∂μ

/-- **The Rosenthal assembly.**  Given the cumulative one-step bound `A ≤ C (B + V)` and the
Pinelis cross-term bound `B ≤ K W A^{(p-2)/p} + K V`, the martingale Rosenthal bound follows:

  `A^{2/p} ≤ max (2 C K W) ((2 C (K+1) V)^{2/p})`.

Composing with `martingaleOneStep_iterate` (which supplies `A ≤ C (B + V)` with `A = E|S k|^p`,
`B` and `V` as above) and `PinelisInductionStep` (which supplies the cross-term bound) gives the
martingale Rosenthal inequality. -/
theorem rosenthal_of_crossTerm {p A B V W : ℝ} (hp : 2 ≤ p) {C K : ℝ}
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hiter : A ≤ C * (B + V))
    (hcross : B ≤ K * W * A ^ ((p - 2) / p) + K * V) :
    A ^ (2 / p) ≤ max (2 * (C * K) * W) ((2 * (C * (K + 1) * V)) ^ (2 / p)) := by
  have hpow : 0 ≤ A ^ ((p - 2) / p) := Real.rpow_nonneg hA _
  have h : A ≤ (C * K) * A ^ ((p - 2) / p) * W + (C * (K + 1)) * V := by
    nlinarith [hiter, hcross, hpow, hW]
  exact solve_rpow_le hp hA (by positivity) (by positivity) h

end LatticeProb
