/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRoundCutoffTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceFullHalf
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceCutoffCarriers

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

def j1RoundCutLowerEvent {Ω : Type u} [MeasurableSpace Ω] (ξ : ℝ)
    (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n m : ℕ) (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | ENNReal.ofReal
      (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
      crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
        (j1SourceCross K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b) <
      ENNReal.ofReal (T⁻¹ * ((2 : ℝ)⁻¹ ^ K * L))}

def j1RoundCutUpperEvent {Ω : Type u} [MeasurableSpace Ω]
    (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (hW : IsWhiteNoise P W) (K n m : ℕ)
    (T L : ℝ) (b : ℤ × ℤ) : Set Ω :=
  {ω | ENNReal.ofReal (T * ((2 : ℝ)⁻¹ ^ K * L)) <
      ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        (lfppContMetric ξ (fun z => psiMN Q W P 0 n z ω)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b)}

theorem j1_source_round_cutoff_transfer
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) (ξ : ℝ) (hξ : 0 < ξ)
    (K n m : ℕ) (hm : m + 1 ≤ K)
    (hr : j1SourceRadius Q K ≤ 1 / 4)
    (T L : ℝ) (hT : 1 < T) :
    let I := j1SourceIdx K (j1SourceRadius Q K)
    let bad := {ω | (1 / (2 * ξ) : ℝ) * Real.log T ≤ T20C.Xbig Q W P ω}
    P {ω | ∃ b ∈ I, ω ∈ j1RoundCutLowerEvent ξ Q W P K n m T L b} ≤
      P {ω | ∃ b ∈ I,
        ω ∈ j1RoundFullLowerEvent ξ W P K n m (T^(1 / 2 : ℝ)) L b} +
      P bad ∧
    P {ω | ∃ b ∈ I, ω ∈ j1RoundCutUpperEvent ξ Q W P hW K n m T L b} ≤
      P {ω | ∃ b ∈ I,
        ω ∈ j1RoundFullUpperEvent ξ W P hW K n m (T^(1 / 2 : ℝ)) L b} +
      P bad := by
  dsimp only
  let I := j1SourceIdx K (j1SourceRadius Q K)
  let d := (2 : ℝ)⁻¹ ^ K * L
  let w : (ℤ × ℤ) → Ω → ℝ≥0∞ :=
    fun b ω => ENNReal.ofReal
      (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω))
  have hcar : ∀ b ∈ I,
      j1SourceCross K m b ⊆ T20D.bigBox ∧
      LaneCInputs.sourceAround K m b ⊆ T20D.bigBox := by
    intro b hb
    exact j1_source_round_cutoff_carriers Q K m hm hr b hb
  obtain ⟨hδ, hδeq⟩ := j1_half_cutoff_delta ξ hξ
  have htr := j1_cutoff_indexed_transfer P W hW Q ξ n I
    (fun b => j1SourceCross K m b)
    (fun b => LaneCInputs.sourceAround K m b)
    (fun b => LaneCInputs.sourceInner K m b)
    (fun b => LaneCInputs.sourceOuter K m b)
    (fun b hb => (hcar b hb).1) (fun b hb => (hcar b hb).2)
    w (1 / (2 * ξ)) T hδ hT
    (ENNReal.ofReal (T⁻¹ * d))
    (ENNReal.ofReal (T^(1 / 2 : ℝ) * d))
  have hlow := htr.1
  have hupp := htr.2
  constructor
  · simpa only [I, w, d, j1RoundCutLowerEvent,
      j1RoundFullLowerEvent, Set.mem_ofPred_eq, hδeq,
      j1_half_cutoff_low_threshold T
        ((2 : ℝ)⁻¹ ^ K * L) (by linarith)] using hlow
  · simpa only [I, w, d, j1RoundCutUpperEvent,
      j1RoundFullUpperEvent, Set.mem_ofPred_eq, hδeq,
      j1_half_cutoff_high_threshold T
        ((2 : ℝ)⁻¹ ^ K * L) (by linarith)] using hupp

end SupercriticalLQGUniqueness.B2.DG20Conc
