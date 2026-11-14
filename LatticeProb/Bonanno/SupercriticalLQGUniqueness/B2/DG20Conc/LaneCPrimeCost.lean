/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeChain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeAround

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

theorem laneC_prime_chain_cost_le {ξ : ℝ} {f : ℂ → ℝ}
    (side : Fin 4) (p : Fin 5 → ℝ → ℂ) (d : Fin 4 → ℝ → ℂ)
    (hp : ∀ i, AdmPath (laneCPrimeLongRect side i).toSet
      (laneCPrimeLongRect side i).side₁
      (laneCPrimeLongRect side i).side₂ (p i))
    (hd : ∀ i, AdmPath (laneCPrimeJoinRect side i).toSet
      (laneCPrimeJoinRect side i).side₁
      (laneCPrimeJoinRect side i).side₂ (d i))
    {B : ENNReal}
    (hpl : ∀ i, lfppLen ξ f (p i) ≤ B)
    (hdl : ∀ i, lfppLen ξ f (d i) ≤ B) :
    ∃ r : ℝ → ℂ,
      AdmPath (laneCPrimeWideRect side).toSet
        (laneCPrimeWideRect side).side₁
        (laneCPrimeWideRect side).side₂ r ∧
      lfppLen ξ f r ≤ 9 * B := by
  obtain ⟨r,hr,hlen⟩ := laneC_prime_five_chain (ξ := ξ) (f := f)
    side p d hp hd
  refine ⟨r,hr,hlen.trans ?_⟩
  calc
    (((lfppLen ξ f (p 0) + lfppLen ξ f (d 0) + lfppLen ξ f (p 1)) +
        lfppLen ξ f (d 1) + lfppLen ξ f (p 2)) +
        lfppLen ξ f (d 2) + lfppLen ξ f (p 3)) +
        lfppLen ξ f (d 3) + lfppLen ξ f (p 4) ≤
      (((B + B + B) + B + B) + B + B) + B + B := by
        gcongr <;> first | exact hpl _ | exact hdl _
    _ = 9 * B := by ring

theorem laneC_prime_paths_aroundDist_le {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f)
    (p : Fin 4 → Fin 5 → ℝ → ℂ) (d : Fin 4 → Fin 4 → ℝ → ℂ)
    (hp : ∀ side i, AdmPath (laneCPrimeLongRect side i).toSet
      (laneCPrimeLongRect side i).side₁
      (laneCPrimeLongRect side i).side₂ (p side i))
    (hd : ∀ side i, AdmPath (laneCPrimeJoinRect side i).toSet
      (laneCPrimeJoinRect side i).side₁
      (laneCPrimeJoinRect side i).side₂ (d side i))
    {B : ENNReal}
    (hpl : ∀ side i, lfppLen ξ f (p side i) ≤ B)
    (hdl : ∀ side i, lfppLen ξ f (d side i) ≤ B) :
    (lfppContMetric ξ f hf).aroundDist laneCPrimeAround
      laneCPrimeInner laneCPrimeOuter ≤ 36 * B := by
  choose r hr hlen using fun side => laneC_prime_chain_cost_le
    (ξ := ξ) (f := f) side (p side) (d side)
      (hp side) (hd side) (hpl side) (hdl side)
  have hbase := laneC_four_prime_wide_aroundDist_le (ξ := ξ) (f := f) hf
    (hr 0) (hr 1) (hr 2) (hr 3)
  calc
    _ ≤ lfppLen ξ f (r 0) + lfppLen ξ f (r 1) +
        lfppLen ξ f (r 2) + lfppLen ξ f (r 3) := hbase
    _ ≤ 9 * B + 9 * B + 9 * B + 9 * B := by
      gcongr <;> exact hlen _
    _ = 36 * B := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
