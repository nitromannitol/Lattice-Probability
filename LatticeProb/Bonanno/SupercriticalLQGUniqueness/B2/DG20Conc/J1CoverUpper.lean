/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoverUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Union

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.LFPP

theorem j1_cover_upper_of_rect_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℂ → Ω → ℝ) (hYc : ∀ ω, Continuous (fun z => Y z ω))
    {ξ b q N : ℝ} {ks kl : ℕ} {Ucross Uaround E F : Set ℂ}
    (hgeom : LaneCRepairedInputs.RectAnnulusCoverAt
      Ucross Uaround E F ks kl N)
    (htail : ∀ (u : Circle) (c : ℂ),
      P {ω | b < T20B.mrectLen ξ (fun z => Y z ω) kl u c 3 1} ≤
        ENNReal.ofReal q) :
    P {ω | ENNReal.ofReal (N * b) <
      (lfppContMetric ξ (fun z => Y z ω) (hYc ω)).aroundDist
        Uaround E F} ≤ ENNReal.ofReal N * ENNReal.ofReal q := by
  obtain ⟨Js, Jl, us, ul, cs, cl, hJs, hJl, hcover⟩ := hgeom
  have hcount : (Jl.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hJl
  have hsubset :
      {ω | ENNReal.ofReal (N * b) <
        (lfppContMetric ξ (fun z => Y z ω) (hYc ω)).aroundDist
          Uaround E F} ⊆
      {ω | ∃ j ∈ Jl, b < T20B.mrectLen ξ
        (fun z => Y z ω) kl (ul j) (cl j) 3 1} := by
    intro ω hω
    exact (hcover ξ (fun z => Y z ω) (hYc ω) 0 b).2 hω
  calc
    P {ω | ENNReal.ofReal (N * b) <
        (lfppContMetric ξ (fun z => Y z ω) (hYc ω)).aroundDist
          Uaround E F} ≤
      P {ω | ∃ j ∈ Jl, b < T20B.mrectLen ξ
        (fun z => Y z ω) kl (ul j) (cl j) 3 1} :=
          measure_mono hsubset
    _ = P (⋃ j ∈ Jl, {ω | b < T20B.mrectLen ξ
        (fun z => Y z ω) kl (ul j) (cl j) 3 1}) := by
          congr 1; ext ω; simp
    _ ≤ (Jl.card : ℝ≥0∞) * ENNReal.ofReal q := by
      refine (measure_biUnion_finset_le Jl _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j _ => htail (ul j) (cl j)
    _ ≤ ENNReal.ofReal N * ENNReal.ofReal q :=
      mul_le_mul_of_nonneg_right hcount (zero_le : (0 : ℝ≥0∞) ≤ _)

end SupercriticalLQGUniqueness.B2.DG20Conc
