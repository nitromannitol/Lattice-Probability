/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39I4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9 on complete spaces: `T39JRestData`, `CONFThm3_9IterC'` (DEC-120 §5, packet J5)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1506–1744. Assembly (copy-and-adapt of S3T39I5 and of `confThm3_9At_of_iterAE`, S3T39I2, by
P2-CONFT39c) with the D120 restatement:

* `T39JRestData` (D120 §5): the inputs of `t39j_iterData_of` (S3T39J5b) for one arc family —
  radii `s_k` with the a.s. recursion, `Measurable (s k)`, a.s. stopping times, a.s. inclusions
  `𝓕_k ⊆ 𝓕_{k+1}`, a.s. measurability of `n_k`, `x_{k,i}`, `Act k i`, and (3.21′);
* `CONFThm3_9IterC'`, `confThm3_9AtC_of_iterAE`: `CONFThm3_9Iter'` / `confThm3_9At_of_iterAE` on
  complete spaces, for `τ` with `𝓑^•_τ` local modulo additive constants (D130).

The remaining node is `CONFThm3_9RestCL` (S3T39J9); the assembly `CONFThm3_9At` from it is
`confThm3_9At_of_restCL` (S3T39J11). The former node `CONFThm3_9RestC` (without the D130
locality hypothesis on `τ`) was removed (D130; it is false for `p.A < 0`, handoff/P2-CONFJ6.md).

`AEMeasurable[𝓕_k] f P` of the D120 §5 text does not typecheck in Lean (`AEMeasurable[m]` fixes
the σ-algebra of the measure, `P` lives on `mΩ`); the fields are written in the meaning D120 §5
gives, `∃ g, Measurable[𝓕_k] g ∧ f =ᵐ[P] g`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Classical in
/-- the inputs of `t39j_iterData_of` for one arc family, apart from Lemma 3.7, `hgood`, `hN₀`
(DEC-120 §5) -/
def T39JRestData (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (χ a : ℝ)
    (N₁ : ℕ) {Ω : Type} [m0 : MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (z₀ : ℂ)
    (R : ℝ) {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ) : Prop :=
  ∃ (s : ℕ → Ω → ℝ) (n : ℕ → Ω → ℕ) (x : ℕ → ι → Ω → ℂ) (Act : ℕ → ι → Set Ω),
    (∀ i ω, I₀ i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω))) ∧
    (∀ ω, s 0 ω = τ ω) ∧
    (∀ k, ∀ᵐ ω ∂P, ENNReal.ofReal (s (k + 1) ω) = confSigma (xiGamma γ) c D P h p z₀ R
        ((2 : ℝ)⁻¹ ^ t39gExp (n k ω)) (s k ω) ω) ∧
    (∀ k ω, n k ω = (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty).card) ∧
    (∀ k ω, 0 ≤ s k ω) ∧ (∀ k, Measurable (s k)) ∧
    (∀ k, IsFilledBallStoppingTimeAE P D h z₀ (s k)) ∧
    (∀ k, IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (s k ω))) ∧
    (∀ k, ∀ A : Set Ω, MeasurableSet[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))] A →
      AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s (k + 1) ω))) A) ∧
    (∀ k, ∃ g : Ω → ℕ,
      Measurable[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))] g ∧ n k =ᵐ[P] g) ∧
    (∀ k i, ∃ g : Ω → ℂ,
      Measurable[filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))] g ∧
        x k i =ᵐ[P] g) ∧
    (∀ k i, ∀ᵐ ω ∂P, x k i ω ∈ frontier (filledBall (D (h ω)) z₀ (s k ω))) ∧
    (∀ k i, AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω))) (Act k i)) ∧
    (∀ k i ω, ω ∈ Act k i → 1 ≤ t39gExp (n k ω) ∧
      (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧
      x k i ω ∈ frontier (filledBall (D (h ω)) z₀ (s k ω)) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < (2 : ℝ)⁻¹ ^ t39gExp (n k ω) * R ∧
        DisconnectsFromInfty (filledBall (D (h ω)) z₀ (s k ω)) (ball (x k i ω) ρ)
          (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω))) ∧
    (∀ᵐ ω ∂P, ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a → ∀ k,
      s k ω < tauR D h z₀ (3 * R) ω → N₁ ≤ n k ω → 4 * (Finset.univ.filter fun i =>
        (t39gArc (D (h ω)) z₀ (s k ω) (I₀ i ω)).Nonempty ∧ ω ∉ Act k i).card ≤ n k ω)

/-- `CONFThm3_9Iter'` (S3T39I2) on complete probability spaces -/
def CONFThm3_9IterC' (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (χ : ℝ) :
    Prop :=
  ∃ α C₀ : ℝ, 0 < α ∧ 0 ≤ C₀ ∧ ∀ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      (∀ᵐ ω ∂P, 0 < τ ω ∧ Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω))) ∧
      ∃ A : (m : ℕ) → Fin m → Ω → Set ℂ,
        (∀ᵐ ω ∂P, ∀ F : Finset ℂ, (F : Set ℂ) ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
          ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ A m i ω) ∧
            ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ A m i ω → y ∈ A m i ω → x = y) ∧
        ∀ m, T39IterData' γ D c p χ α C₀ a N₀ P h z₀ R (A m) τ

open Classical in
/-- **CONF Theorem 3.9 on complete spaces** from its almost sure iteration inputs; copy of
`confThm3_9At_of_iterAE` (S3T39I2) with `[P.IsComplete]` -/
theorem confThm3_9AtC_of_iterAE {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {χ : ℝ} (hχ : 0 < χ) (hc : ∀ r, 0 < r → 0 < c r) (H : CONFThm3_9IterC' γ D c p χ) :
    CONFThm3_9AtC γ D c p χ := by
  obtain ⟨α, C₀, hα, hC₀, H⟩ := H
  refine ⟨1, χ / 8 / 4, one_pos, by positivity, fun a ha => ?_⟩
  obtain ⟨N₀, HN⟩ := H a ha
  obtain ⟨b₀, hb₀, harcs⟩ := t39i_arcs (γ := γ) (D := D) (c := c) (p := p) hχ hα hC₀ ha.1
    ha.2.le N₀
  refine ⟨b₀, hb₀, ?_⟩
  intro Ω _ P _ _ h hh z₀ R hR N hN τ hτst hloc hτI
  obtain ⟨hτb, A, hsep, hdata⟩ := HN P h hh z₀ R hR τ hτst hloc hτI
  have hS : ∀ ω, 0 < scaleFac (xiGamma γ) c (h ω) R z₀ := fun ω =>
    mul_pos (hc R hR) (Real.exp_pos _)
  have hτ2 : ∀ᵐ ω ∂P, τ ω ≤ tauR D h z₀ (2 * R) ω := hτI.mono fun ω hω => hω.2
  set E := confReg (xiGamma γ) c D P h p χ z₀ R a
  set X : Ω → Set ℂ := fun ω => hitSetLM (D (h ω)) z₀ (τ ω)
    (τ ω + (N : ℝ) ^ (-(χ / 8 / 4)) * scaleFac (xiGamma γ) c (h ω) R z₀)
  set Ωs : Set Ω := {ω | ∀ F : Finset ℂ, (F : Set ℂ) ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
    ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ A m i ω) ∧
      ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ A m i ω → y ∈ A m i ω → x = y}
  have hB : ∀ m, P {ω | ω ∈ E ∩ Ωs ∧ N ≤ (Finset.univ.filter fun i =>
      (A m i ω ∩ X ω).Nonempty).card} ≤
      ENNReal.ofReal (b₀ * Real.exp (-(N : ℝ) ^ (χ / 8 / 4))) := by
    intro m
    obtain ⟨s, n, 𝓕, Act, G, hI₀, hs0, hsucc, hn, hmono, h𝓕, hnm, hActm, hGm, hcond, hActAl,
      hstar, hkill⟩ := hdata m
    have h1 := harcs P h z₀ R hR (A m) τ s n 𝓕 Act G hτb hI₀ hτ2 hS hs0 hsucc hn hmono h𝓕 hnm
      hActm hGm hcond hActAl hstar hkill N hN
    refine (measure_mono ?_).trans h1
    intro ω hω
    exact ⟨hω.1.1, hω.2⟩
  have hpts := t39g_points_of_arcs P (E ∩ Ωs) X A N _
    (fun ω hω F hF => hω.2 F (hF.trans fun x hx => hx.1)) hB
  have hfin : {ω | ω ∈ E ∧ ((N : ℕ∞) : ℕ∞) < (X ω).encard} ≤ᵐ[P]
      {ω | ω ∈ E ∩ Ωs ∧ ((N : ℕ∞) : ℕ∞) < (X ω).encard} := by
    filter_upwards [hsep] with ω hωs hω
    exact ⟨⟨hω.1, hωs⟩, hω.2⟩
  refine (measure_mono_ae hfin).trans (hpts.trans (le_of_eq ?_))
  congr 2
  ring_nf

end CONF
end LQGMetric
