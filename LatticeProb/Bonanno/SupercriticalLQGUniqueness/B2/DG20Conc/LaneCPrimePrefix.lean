/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimePrefix at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBridgeGeneric

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

def laneCPrimePrefixRect (side : Fin 4) (i : Fin 5) : MarkedRect :=
  let w : ℝ := (i.val : ℝ) / 4 + 3 / 8
  match side.val with
  | 0 => ⟨-3 / 16, 17 / 16, w, 1 / 8, true⟩
  | 1 => ⟨-3 / 16, -3 / 16, w, 1 / 8, true⟩
  | 2 => ⟨-3 / 16, -3 / 16, 1 / 8, w, false⟩
  | _ => ⟨17 / 16, -3 / 16, 1 / 8, w, false⟩

def laneCPrimeJoinMidRect (side : Fin 4) (i : Fin 4) : MarkedRect :=
  let t : ℝ := -3 / 16 + ((i.val : ℝ) + 1) / 4
  match side.val with
  | 0 => ⟨t, 17 / 16, 1 / 8, 1 / 8, false⟩
  | 1 => ⟨t, -3 / 16, 1 / 8, 1 / 8, false⟩
  | 2 => ⟨-3 / 16, t, 1 / 8, 1 / 8, true⟩
  | _ => ⟨17 / 16, t, 1 / 8, 1 / 8, true⟩

def laneCPrimeFin4AsFin5 (i : Fin 4) : Fin 5 := ⟨i.val, by omega⟩

theorem laneC_prime_prefix_zero (side : Fin 4) :
    laneCPrimePrefixRect side 0 = laneCPrimeLongRect side 0 := by
  fin_cases side <;>
    norm_num [laneCPrimePrefixRect, laneCPrimeLongRect]

theorem laneC_prime_prefix_four (side : Fin 4) :
    laneCPrimePrefixRect side 4 = laneCPrimeWideRect side := by
  fin_cases side <;>
    norm_num [laneCPrimePrefixRect, laneCPrimeWideRect]

theorem laneC_prime_prefix_subset_next (side : Fin 4) (i : Fin 4) :
    (laneCPrimePrefixRect side (laneCPrimeFin4AsFin5 i)).toSet ⊆
      (laneCPrimePrefixRect side i.succ).toSet := by
  fin_cases side <;> fin_cases i <;> intro z hz <;>
    norm_num [laneCPrimeFin4AsFin5, laneCPrimePrefixRect, MarkedRect.toSet,
      Complex.mem_reProdIm] at hz ⊢ <;>
    rcases hz with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩,⟨by linarith, by linarith⟩⟩

theorem laneC_prime_long_next_subset (side : Fin 4) (i : Fin 4) :
    (laneCPrimeLongRect side i.succ).toSet ⊆
      (laneCPrimePrefixRect side i.succ).toSet := by
  fin_cases side <;> fin_cases i <;> intro z hz <;>
    norm_num [laneCPrimePrefixRect, laneCPrimeLongRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at hz ⊢ <;>
    rcases hz with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩,⟨by linarith, by linarith⟩⟩

theorem laneC_prime_join_mid_subset_next (side : Fin 4) (i : Fin 4) :
    (laneCPrimeJoinMidRect side i).toSet ⊆
      (laneCPrimePrefixRect side i.succ).toSet := by
  fin_cases side <;> fin_cases i <;> intro z hz <;>
    norm_num [laneCPrimePrefixRect, laneCPrimeJoinMidRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at hz ⊢ <;>
    rcases hz with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩,⟨by linarith, by linarith⟩⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
