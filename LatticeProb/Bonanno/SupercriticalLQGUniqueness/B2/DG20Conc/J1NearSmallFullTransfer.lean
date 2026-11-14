/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1NearSmallFullTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarsePhi
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1IndexedTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearbyIdx
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusCompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockCrossLaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem j1_nearby_small_full_field_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n)
    (i : Bool) (M : ℝ) (tLow tHigh : ℝ≥0∞) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * M))
    let Bad : Set Ω := {ω | ∃ b ∈ j1NearbyIdx K,
      ∃ z ∈ laneBBlockAnnulus i (T20.dyCenter K b) K,
        M < |phiMN W P 0 K z ω -
          phiMN W P 0 K (T20.dyCenter K b) ω|}
    P {ω | ∃ b ∈ j1NearbyIdx K,
      ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        crossLenIn ξ (fun z => phiMN W P 0 n z ω)
          (laneBBlockAnnulus i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K) < tLow} ≤
      P {ω | ∃ b ∈ j1NearbyIdx K,
        crossLenIn ξ (fun z => phiMN W P K n z ω)
          (laneBBlockAnnulus i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K) < e * tLow} +
        P Bad ∧
    P {ω | ∃ b ∈ j1NearbyIdx K,
      e * tHigh <
        ENNReal.ofReal
          (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
          ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (laneBBlockAround i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K)} ≤
      P {ω | ∃ b ∈ j1NearbyIdx K,
        tHigh <
        (lfppContMetric ξ (fun z => phiMN W P K n z ω)
          ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
          (laneBBlockAround i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K)} +
        P Bad := by
  dsimp only
  let J := j1NearbyIdx K
  let Uc : ℤ × ℤ → Set ℂ :=
    fun b => laneBBlockAnnulus i (T20.dyCenter K b) K
  let Ua : ℤ × ℤ → Set ℂ :=
    fun b => laneBBlockAround i (T20.dyCenter K b) K
  let E : ℤ × ℤ → Set ℂ :=
    fun b => j1BlockInner i (T20.dyCenter K b) K
  let F : ℤ × ℤ → Set ℂ :=
    fun b => j1BlockOuter i (T20.dyCenter K b) K
  let e := ENNReal.ofReal (Real.exp (|ξ| * M))
  let Bad : Set Ω := {ω | ∃ b ∈ J, ∃ z ∈ Uc b,
    M < |phiMN W P 0 K z ω -
      phiMN W P 0 K (T20.dyCenter K b) ω|}
  have hsub (b : ℤ × ℤ) : Ua b ⊆ Uc b :=
    image_mono (laneC_unit_around_subset_cross i)
  have hcomp : ∀ᵐ ω ∂P, ω ∉ Bad → ∀ b ∈ J,
      crossLenIn ξ (fun z => phiMN W P K n z ω) (Uc b) (E b) (F b) ≤
        e * (ENNReal.ofReal
          (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
          crossLenIn ξ (fun z => phiMN W P 0 n z ω)
            (Uc b) (E b) (F b)) ∧
      ENNReal.ofReal
          (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
          ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (Ua b) (E b) (F b) ≤
        e * (lfppContMetric ξ (fun z => phiMN W P K n z ω)
          ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
          (Ua b) (E b) (F b) := by
    filter_upwards [j1_ae_coarse_phi_normalized_comparison
      P W hW ξ hKn] with ω hω
    intro hnBad b hb
    have hc : ∀ z ∈ Uc b,
        |phiMN W P 0 K z ω -
          phiMN W P 0 K (T20.dyCenter K b) ω| ≤ M := by
      intro z hz
      exact le_of_not_gt (fun h => hnBad ⟨b, hb, z, hz, h⟩)
    have ha : ∀ z ∈ Ua b,
        |phiMN W P 0 K z ω -
          phiMN W P 0 K (T20.dyCenter K b) ω| ≤ M :=
      fun z hz => hc z (hsub b hz)
    exact ⟨(hω (Uc b) (E b) (F b)
      (T20.dyCenter K b) M hc).1,
      (hω (Ua b) (E b) (F b)
        (T20.dyCenter K b) M ha).2⟩
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heTop : e ≠ ∞ := ENNReal.ofReal_ne_top
  simpa only [J, Uc, Ua, E, F, e, Bad] using
    (j1_indexed_tail_transfer_of_ae_compare P J
      (fun b ω => crossLenIn ξ (fun z => phiMN W P K n z ω)
        (Uc b) (E b) (F b))
      (fun b ω => ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        crossLenIn ξ (fun z => phiMN W P 0 n z ω)
          (Uc b) (E b) (F b))
      (fun b ω => (lfppContMetric ξ
        (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (Ua b) (E b) (F b))
      (fun b ω => ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
          ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
          (Ua b) (E b) (F b))
      Bad e tLow tHigh he0 heTop hcomp)

end SupercriticalLQGUniqueness.B2.DG20Conc
