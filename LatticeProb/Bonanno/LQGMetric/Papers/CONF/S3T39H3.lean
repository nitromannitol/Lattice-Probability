/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39H3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412gTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: tools for the iteration inputs from Lemma 3.7

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
proof of Theorem 3.9, C:1595–1617.

* `t39h_inter_localSigma0`: trace of `σ(A, h|_A)` mod constants on an event where `A = A'`
  (the mod-constant form of `GM.p412g_inter_localSigma`, same proof);
* `t39h_fbs0_eq`: `filledBallSigmaAt0` at a real radius `s ≥ 0` is `localSigma0` of `𝓑^•_s`;
* `t39h_le_iter`: the iterated radii `s_k` are `≥ τ` (C:1530);
* **`t39h_kill_of_propA`**: the kill step C:1600–1602 at one `ω` from property A of
  `CONFLem3_7AtAE0` (with (3.22) from `t39g_confRK_le_ediam`).
-/

noncomputable section

open MeasureTheory MeasurableSpace Set Metric
open LQGMetric.Blueprint LQGMetric.GM
open scoped ENNReal

namespace LQGMetric
namespace CONF

section Trace
variable {Ω : Type}

/-- `filledBallSigmaAt0` at a real radius `s ≥ 0` -/
theorem t39h_fbs0_eq (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {s : Ω → ℝ}
    (hs : ∀ ω, 0 ≤ s ω) :
    filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s ω)) =
      localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (s ω)) := by
  unfold filledBallSigmaAt0
  congr 1
  funext ω
  simp only [filledBallE, ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal (hs ω)]

end Trace

section NullAug
variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- the events a.s. equal to an event of `m` -/
def t39hAESig (P : Measure[m0] Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, Filter.EventuallyEq.rfl⟩
  measurableSet_compl A := fun ⟨B, hB, hAB⟩ => ⟨Bᶜ, hB.compl, hAB.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB hfB using hf
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, Filter.EventuallyEqSet.countable_iUnion hfB⟩

end NullAug

/-- the iterated radii are `≥ τ` -/
theorem t39h_le_iter {Ω : Type} [MeasurableSpace Ω] {ξ : ℝ} {cc : ℝ → ℝ}
    {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC} {p : CONFParams} {z₀ : ℂ} {R : ℝ}
    {s : ℕ → Ω → ℝ} {e : ℕ → Ω → ℝ} {ω : Ω} (h0 : 0 < s 0 ω)
    (hsucc : ∀ k, ENNReal.ofReal (s (k + 1) ω) = confSigma ξ cc D P h p z₀ R (e k ω) (s k ω) ω) :
    ∀ k, s 0 ω ≤ s k ω := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have h1 := t39g_le_confSigma ξ cc D P h p z₀ R (e k ω) (s k ω) ω
    rw [← hsucc k] at h1
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h1 with h2 | h2
    · exact ih.trans h2
    · linarith

/-- **the kill step C:1600–1602 from Lemma 3.7 A** (true form): on `𝓔_𝕣(a)`, for
`τ_𝕣 ≤ s < τ_{3𝕣}`, `ε = 2^{−m}` with `7ε^{1/2} ≤ a`, `t′ = σ^ε_{s,𝕣}`, and `B_ρ(x)`, `ρ < ε𝕣`,
disconnecting `I^{(s)}` from `∞`, property A kills `I^{(t′)}` -/
theorem t39h_kill_of_propA {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {χ : ℝ} {z₀ : ℂ}
    {R a : ℝ} {ω : Ω} (hω : ω ∈ confReg (xiGamma γ) c D P h p χ z₀ R a) (hR : 0 < R)
    (ha : 0 < a) {m : ℕ} (hm : 7 * ((2 : ℝ)⁻¹ ^ m) ^ (1 / 2 : ℝ) ≤ a) {s : Ω → ℝ}
    {x : Ω → ℂ} {e : Ω → ℝ} (he : e ω = (2 : ℝ)⁻¹ ^ m) {τ t' : ℝ} {I : Set ℂ}
    (hτ0 : 0 < τ) (hτt : τ ≤ s ω) (htR : tauR D h z₀ R ω ≤ s ω)
    (ht3 : s ω < tauR D h z₀ (3 * R) ω)
    (hσ : confSigma (xiGamma γ) c D P h p z₀ R ((2 : ℝ)⁻¹ ^ m) (s ω) ω = ENNReal.ofReal t')
    (hgeo : ∀ w, ∃ (Q : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) Q L z₀ w)
    (hbd : ∀ s' : ℝ, Bornology.IsBounded (ballM (D (h ω)) z₀ s'))
    (hI : I ⊆ frontier (filledBall (D (h ω)) z₀ τ))
    (hx : x ω ∈ frontier (filledBall (D (h ω)) z₀ (s ω))) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < (2 : ℝ)⁻¹ ^ m * R)
    (hdis : DisconnectsFromInfty (filledBall (D (h ω)) z₀ (s ω)) (ball (x ω) ρ)
      (t39gArc (D (h ω)) z₀ (s ω) I))
    (hA : T39HPropA γ D c p P h z₀ R s x e ω) :
    t39gArc (D (h ω)) z₀ t' I = ∅ := by
  have ht0 : 0 < s ω := hτ0.trans_le hτt
  have htt' : s ω ≤ t' := by
    have h1 := t39g_le_confSigma (xiGamma γ) c D P h p z₀ R ((2 : ℝ)⁻¹ ^ m) (s ω) ω
    rw [hσ] at h1
    rcases ENNReal.ofReal_le_ofReal_iff'.1 h1 with h2 | h2
    · exact h2
    · linarith
  have hK3 := t39g_filledBall_subset_of_lt_tauR ht0 ht3
  have hKa : ball z₀ (a * R) ⊆ filledBall (D (h ω)) z₀ (s ω) :=
    hω.1.trans (gm_filledBall_mono _ _ htR)
  have hdiam := t39g_confRK_le_ediam hω hR ha hm hK3 hKa
  unfold T39HPropA at hA
  rw [he] at hA
  have hk := hA (t39gArc (D (h ω)) z₀ (s ω) I) ρ ht0 hgeo hbd hx (fun z hz => hz.1) hρ0 hρ
    hdis hdiam
  refine t39g_kill hτ0 hτt htt' (hbd τ) hI fun y Q L hy hQ u hu => hk y Q L ?_ hQ u hu
  rw [hσ]
  simpa only [filledBallE, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal (ht0.le.trans htt')] using hy

end CONF
end LQGMetric
