/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Union at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Large

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem laneA2_cover_tail_of_rect_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ a b qlo qhi N : ℝ} {ks kl m : ℕ}
    {Ucross Uaround E F : Set ℂ}
    (hgeom : LaneCRepairedInputs.RectAnnulusCoverAt
      Ucross Uaround E F ks kl N)
    (hlow : ∀ (u : Circle) (c : ℂ),
      P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
        ks u c 1 3 < a} ≤ ENNReal.ofReal qlo)
    (hupp : ∀ (u : Circle) (c : ℂ),
      P {ω | b < T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
        kl u c 3 1} ≤ ENNReal.ofReal qhi) :
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
      Ucross E F < ENNReal.ofReal a} ≤
        ENNReal.ofReal N * ENNReal.ofReal qlo ∧
    P {ω | ENNReal.ofReal (N * b) <
      (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
        Uaround E F} ≤ ENNReal.ofReal N * ENNReal.ofReal qhi := by
  obtain ⟨Js, Jl, us, ul, cs, cl, hJs, hJl, hcover⟩ := hgeom
  have hcountS : (Js.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hJs
  have hcountL : (Jl.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hJl
  constructor
  · have hsubset :
        {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          Ucross E F < ENNReal.ofReal a} ⊆
        {ω | ∃ j ∈ Js, T20B.mrectLen ξ
          (fun z => phiMN W P 0 m z ω) ks (us j) (cs j) 1 3 < a} := by
      intro ω hω
      exact (hcover ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω) a b).1 hω
    calc
      P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          Ucross E F < ENNReal.ofReal a} ≤
        P {ω | ∃ j ∈ Js, T20B.mrectLen ξ
          (fun z => phiMN W P 0 m z ω) ks (us j) (cs j) 1 3 < a} :=
            measure_mono hsubset
      _ = P (⋃ j ∈ Js, {ω | T20B.mrectLen ξ
          (fun z => phiMN W P 0 m z ω) ks (us j) (cs j) 1 3 < a}) := by
            congr 1; ext ω; simp
      _ ≤ (Js.card : ℝ≥0∞) * ENNReal.ofReal qlo := by
        refine (measure_biUnion_finset_le Js _).trans ?_
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun j _ => hlow (us j) (cs j)
      _ ≤ ENNReal.ofReal N * ENNReal.ofReal qlo :=
        mul_le_mul_of_nonneg_right hcountS (zero_le : (0 : ℝ≥0∞) ≤ _)
  · have hsubset :
        {ω | ENNReal.ofReal (N * b) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            Uaround E F} ⊆
        {ω | ∃ j ∈ Jl, b < T20B.mrectLen ξ
          (fun z => phiMN W P 0 m z ω) kl (ul j) (cl j) 3 1} := by
      intro ω hω
      exact (hcover ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω) a b).2 hω
    calc
      P {ω | ENNReal.ofReal (N * b) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            Uaround E F} ≤
        P {ω | ∃ j ∈ Jl, b < T20B.mrectLen ξ
          (fun z => phiMN W P 0 m z ω) kl (ul j) (cl j) 3 1} :=
            measure_mono hsubset
      _ = P (⋃ j ∈ Jl, {ω | b < T20B.mrectLen ξ
          (fun z => phiMN W P 0 m z ω) kl (ul j) (cl j) 3 1}) := by
            congr 1; ext ω; simp
      _ ≤ (Jl.card : ℝ≥0∞) * ENNReal.ofReal qhi := by
        refine (measure_biUnion_finset_le Jl _).trans ?_
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun j _ => hupp (ul j) (cl j)
      _ ≤ ENNReal.ofReal N * ENNReal.ofReal qhi :=
        mul_le_mul_of_nonneg_right hcountL (zero_le : (0 : ℝ≥0∞) ≤ _)

end SupercriticalLQGUniqueness.B2.DG20Conc
