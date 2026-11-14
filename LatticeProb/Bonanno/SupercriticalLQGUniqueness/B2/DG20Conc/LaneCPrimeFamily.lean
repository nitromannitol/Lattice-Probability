/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeMotion

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

def laneCPrimeFamilyU (j : Fin 36) : Circle :=
  let side : Fin 4 := ⟨j.val / 9, by omega⟩
  if j.val % 9 < 5 then laneCPrimeLongMotionU side
  else laneCPrimeJoinMotionU side

def laneCPrimeFamilyC (j : Fin 36) : ℂ :=
  let side : Fin 4 := ⟨j.val / 9, by omega⟩
  if h : j.val % 9 < 5 then
    laneCPrimeLongMotionC side ⟨j.val % 9, h⟩
  else laneCPrimeJoinMotionC side ⟨j.val % 9 - 5, by omega⟩

def laneCPrimeLongIndex (side : Fin 4) (i : Fin 5) : Fin 36 :=
  ⟨9 * side.val + i.val, by omega⟩

def laneCPrimeJoinIndex (side : Fin 4) (i : Fin 4) : Fin 36 :=
  ⟨9 * side.val + 5 + i.val, by omega⟩

theorem laneC_prime_family_long (side : Fin 4) (i : Fin 5) :
    laneCPrimeFamilyU (laneCPrimeLongIndex side i) =
        laneCPrimeLongMotionU side ∧
    laneCPrimeFamilyC (laneCPrimeLongIndex side i) =
        laneCPrimeLongMotionC side i := by
  have hdiv : (9 * side.val + i.val) / 9 = side.val := by omega
  have hmod : (9 * side.val + i.val) % 9 = i.val := by omega
  constructor <;>
    simp [laneCPrimeFamilyU, laneCPrimeFamilyC, laneCPrimeLongIndex,
      hdiv, hmod, i.isLt]

theorem laneC_prime_family_join (side : Fin 4) (i : Fin 4) :
    laneCPrimeFamilyU (laneCPrimeJoinIndex side i) =
        laneCPrimeJoinMotionU side ∧
    laneCPrimeFamilyC (laneCPrimeJoinIndex side i) =
        laneCPrimeJoinMotionC side i := by
  have hdiv : (9 * side.val + 5 + i.val) / 9 = side.val := by omega
  have hmod : (9 * side.val + 5 + i.val) % 9 = 5 + i.val := by omega
  have hnot : ¬ 5 + i.val < 5 := by omega
  constructor <;>
    simp [laneCPrimeFamilyU, laneCPrimeFamilyC, laneCPrimeJoinIndex,
      hdiv, hmod, hnot]

theorem laneC_prime_long_family_imp {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {N b : ℝ} (hN : 36 ≤ N)
    (hlarge : ENNReal.ofReal (N * b) <
      (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
        laneCPrimeInner laneCPrimeOuter) :
    ∃ j : Fin 36,
      b < T20B.mrectLen ξ f 3 (laneCPrimeFamilyU j)
        (laneCPrimeFamilyC j) 3 1 := by
  rcases laneC_prime_long_imp hf hN hlarge with h | h
  · obtain ⟨side,i,hi⟩ := h
    refine ⟨laneCPrimeLongIndex side i, ?_⟩
    rw [(laneC_prime_family_long side i).1,
      (laneC_prime_family_long side i).2, ← laneC_prime_long_mrect ξ f side i]
    exact hi
  · obtain ⟨side,i,hi⟩ := h
    refine ⟨laneCPrimeJoinIndex side i, ?_⟩
    rw [(laneC_prime_family_join side i).1,
      (laneC_prime_family_join side i).2, ← laneC_prime_join_mrect ξ f side i]
    exact hi

end SupercriticalLQGUniqueness.B2.DG20Conc
