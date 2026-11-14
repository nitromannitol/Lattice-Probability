/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffIndexed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1IndexedTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLogThreshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem j1_cutoff_indexed_transfer
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) (ξ : ℝ) (n : ℕ) (J : Finset ι)
    (Ucross Uaround E F : ι → Set ℂ)
    (hUcross : ∀ i ∈ J, Ucross i ⊆ T20D.bigBox)
    (hUaround : ∀ i ∈ J, Uaround i ⊆ T20D.bigBox)
    (w : ι → Ω → ℝ≥0∞) (δ T : ℝ) (hδ : 0 < δ) (hT : 1 < T)
    (tLow tHigh : ℝ≥0∞) :
    let e := ENNReal.ofReal (T ^ (δ * |ξ|))
    let bad := {ω | δ * Real.log T ≤ T20C.Xbig Q W P ω}
    P {ω | ∃ i ∈ J,
      w i ω * crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
        (Ucross i) (E i) (F i) < tLow} ≤
      P {ω | ∃ i ∈ J,
        w i ω * crossLenIn ξ (fun z => phiMN W P 0 n z ω)
          (Ucross i) (E i) (F i) < e * tLow} + P bad ∧
    P {ω | ∃ i ∈ J,
      e * tHigh < w i ω *
        (lfppContMetric ξ (fun z => psiMN Q W P 0 n z ω)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (Uaround i) (E i) (F i)} ≤
      P {ω | ∃ i ∈ J,
        tHigh < w i ω *
          (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
            (Uaround i) (E i) (F i)} + P bad := by
  dsimp only
  let e := ENNReal.ofReal (T ^ (δ * |ξ|))
  let bad := {ω | δ * Real.log T ≤ T20C.Xbig Q W P ω}
  have hepos : 0 < e := by
    dsimp [e]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (by linarith) _)
  have heTop : e ≠ ∞ := ENNReal.ofReal_ne_top
  have hfin := T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5
  have hcmp : ∀ᵐ ω ∂P, ω ∉ bad → ∀ i ∈ J,
      w i ω * crossLenIn ξ (fun z => phiMN W P 0 n z ω)
        (Ucross i) (E i) (F i) ≤
        e * (w i ω * crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
          (Ucross i) (E i) (F i)) ∧
      w i ω *
        (lfppContMetric ξ (fun z => psiMN Q W P 0 n z ω)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (Uaround i) (E i) (F i) ≤
        e * (w i ω *
          (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
            (Uaround i) (E i) (F i)) := by
    filter_upwards [hfin] with ω hf hnBad i hi
    have hgood : T20C.Xbig Q W P ω ≤ δ * Real.log T :=
      le_of_lt (lt_of_not_ge hnBad)
    have he : ENNReal.ofReal
        (Real.exp (|ξ| * T20C.Xbig Q W P ω)) ≤ e := by
      calc
        _ ≤ ENNReal.ofReal (Real.exp (|ξ| * (δ * Real.log T))) :=
          laneB_cutoff_factor_le P W Q ξ (δ * Real.log T) ω hgood
        _ = e := laneB_cutoff_factor_log_eq ξ δ T (by linarith)
    have hcross := (laneB_crossLen_compare_cutoff P W Q ξ ω n
      (Ucross i) (E i) (F i) (hUcross i hi) hf).1
    have haround := (laneB_aroundDist_compare_cutoff P W Q ξ ω n
      (Uaround i) (E i) (F i) (hUaround i hi)
      ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω) hf).2
    constructor
    · calc
        _ ≤ w i ω * (ENNReal.ofReal
            (Real.exp (|ξ| * T20C.Xbig Q W P ω)) *
            crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
              (Ucross i) (E i) (F i)) :=
          mul_le_mul_of_nonneg_left hcross bot_le
        _ = ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω)) *
            (w i ω * crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
              (Ucross i) (E i) (F i)) := by ac_rfl
        _ ≤ e * (w i ω * crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
              (Ucross i) (E i) (F i)) :=
          mul_le_mul_of_nonneg_right he bot_le
    · calc
        _ ≤ w i ω * (ENNReal.ofReal
            (Real.exp (|ξ| * T20C.Xbig Q W P ω)) *
            (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
              ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
              (Uaround i) (E i) (F i)) :=
          mul_le_mul_of_nonneg_left haround bot_le
        _ = ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω)) *
            (w i ω *
              (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                (Uaround i) (E i) (F i)) := by ac_rfl
        _ ≤ e * (w i ω *
              (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                (Uaround i) (E i) (F i)) :=
          mul_le_mul_of_nonneg_right he bot_le
  exact j1_indexed_tail_transfer_of_ae_compare P J
    (fun i ω => w i ω * crossLenIn ξ (fun z => phiMN W P 0 n z ω)
      (Ucross i) (E i) (F i))
    (fun i ω => w i ω * crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
      (Ucross i) (E i) (F i))
    (fun i ω => w i ω *
      (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
        (Uaround i) (E i) (F i))
    (fun i ω => w i ω *
      (lfppContMetric ξ (fun z => psiMN Q W P 0 n z ω)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
        (Uaround i) (E i) (F i))
    bad e tLow tHigh hepos.ne' heTop hcmp

end SupercriticalLQGUniqueness.B2.DG20Conc
