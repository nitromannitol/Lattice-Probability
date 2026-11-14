/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1NearbyIdx at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BBlocks
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.D5T

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

open Classical in
def j1NearbyIdx (K : ℕ) : Finset (ℤ × ℤ) :=
  (T20B.nearIdx K).filter
    (fun b => T20.dyCenter K b ∈ j1NearbyBox)

theorem j1_nearbyIdx_mem_nearIdx {K : ℕ} {b : ℤ × ℤ}
    (hb : b ∈ j1NearbyIdx K) : b ∈ T20B.nearIdx K := by
  classical
  exact (Finset.mem_filter.mp hb).1

theorem j1_nearbyIdx_center {K : ℕ} {b : ℤ × ℤ}
    (hb : b ∈ j1NearbyIdx K) :
    T20.dyCenter K b ∈ j1NearbyBox := by
  classical
  exact (Finset.mem_filter.mp hb).2

theorem j1_nearby_union_le_near_union
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (K : ℕ) (E : ℤ × ℤ → Set Ω) :
    P {ω | ∃ b ∈ j1NearbyIdx K, ω ∈ E b} ≤
      P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} :=
  MeasureTheory.measure_mono (by
    rintro ω ⟨b, hb, hω⟩
    exact ⟨b, j1_nearbyIdx_mem_nearIdx hb, hω⟩)

end SupercriticalLQGUniqueness.B2.DG20Conc
