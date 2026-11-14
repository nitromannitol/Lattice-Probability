/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUnitGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeFamily
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeUpper
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortFamily
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open LaneCRepairedInputs

theorem laneC_prime_rect_annulus_cover :
    RectAnnulusCoverAt laneCPrimeCross laneCPrimeAround
      laneCPrimeInner laneCPrimeOuter 3 3 12996 := by
  obtain ⟨Js,us,cs,hsCard,hshort⟩ := laneC_unit_short_family
  let Jl : Finset ℕ := Finset.range 36
  let ul : ℕ → Circle := fun j => if h : j < 36 then
    laneCPrimeFamilyU ⟨j,h⟩ else 1
  let cl : ℕ → ℂ := fun j => if h : j < 36 then
    laneCPrimeFamilyC ⟨j,h⟩ else 0
  refine ⟨Js,Jl,us,ul,cs,cl,hsCard,?_,?_⟩
  · norm_num [Jl]
  · intro ξ f hf a b
    constructor
    · exact hshort false ξ f a
    · intro hlarge
      obtain ⟨j,hj⟩ := laneC_prime_long_family_imp hf
        (by norm_num : (36 : ℝ) ≤ 12996) hlarge
      exact ⟨j.val, Finset.mem_range.mpr j.isLt,
        by simpa [ul,cl,j.isLt] using hj⟩

theorem laneC_double_prime_rect_annulus_cover :
    RectAnnulusCoverAt laneCDoublePrimeCross laneCDoublePrimeAround
      laneCDoublePrimeInner laneCDoublePrimeOuter 3 0 12996 := by
  obtain ⟨Js,us,cs,hsCard,hshort⟩ := laneC_unit_short_family
  let Jl : Finset ℕ := Finset.range 12
  let ul : ℕ → Circle := fun j => if h : j < 12 then
    laneCTwelveMotionU ⟨j,h⟩ else 1
  let cl : ℕ → ℂ := fun j => if h : j < 12 then
    laneCTwelveMotionC ⟨j,h⟩ else 0
  refine ⟨Js,Jl,us,ul,cs,cl,hsCard,?_,?_⟩
  · norm_num [Jl]
  · intro ξ f hf a b
    constructor
    · exact hshort true ξ f a
    · intro hlarge
      obtain ⟨j,hj⟩ := laneC_double_prime_long_mrect_imp hf
        (by norm_num : (12 : ℝ) ≤ 12996) hlarge
      exact ⟨j.val, Finset.mem_range.mpr j.isLt,
        by simpa [ul,cl,j.isLt] using hj⟩

theorem laneC_unit_block_geometry :
    UnitBlockGeometry laneCUnitUcross laneCUnitUaround
      laneCUnitInner laneCUnitOuter := by
  refine ⟨12996, by norm_num, ?_⟩
  intro i
  cases i
  · simpa [laneCUnitUcross, laneCUnitUaround,
      laneCUnitInner, laneCUnitOuter] using laneC_prime_rect_annulus_cover
  · simpa [laneCUnitUcross, laneCUnitUaround,
      laneCUnitInner, laneCUnitOuter] using laneC_double_prime_rect_annulus_cover

end SupercriticalLQGUniqueness.B2.DG20Conc
