/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBoundaryDetour at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EGlue
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EFinal

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.DDDF.T20E LQGMetric.LFPP

theorem laneC_one_boundary_detour_le {ξ : ℝ} {f g : ℂ → ℝ} {Fr : Set ℂ}
    (hfg : ∀ x ∈ Fr, g x = f x)
    {γ ρ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
      (rectAB 1 1).side₂ γ)
    (hγfin : lfppLen ξ f γ ≠ ⊤)
    (hρ : IsPiecewiseC1Path ρ (ρ 0) (ρ 1))
    (hρfin : lfppLen ξ f ρ ≠ ⊤)
    (hρsq : ∀ t ∈ Icc (0 : ℝ) 1,
      ρ t ∈ (rectAB 1 1).toSet ∩ Fr)
    {t₀ t₁ s₀ s₁ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (htord : t₀ ≤ t₁)
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1)
    (hstart : (γ t₀ = ρ s₀ ∧
        ∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ (rectAB 1 1).toSet ∩ Fr) ∨
      (t₀ = 0 ∧ ρ s₀ ∈ (rectAB 1 1).side₁))
    (hend : (γ t₁ = ρ s₁ ∧
        ∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ (rectAB 1 1).toSet ∩ Fr) ∨
      (t₁ = 1 ∧ ρ s₁ ∈ (rectAB 1 1).side₂)) :
    (rectLen ξ g (rectAB 1 1)).toReal ≤
      (lfppLen ξ f γ).toReal + (lfppLen ξ f ρ).toReal := by
  classical
  let e : Circle × ℂ := (1, 0)
  let pc : Circle × ℂ → ℝ → ℂ := fun _ => ρ
  obtain ⟨z, hz, w, hw, hpath, hU⟩ := hγ
  have hz₀ : γ 0 ∈ (rectAB 1 1).side₁ := by rw [hpath.source]; exact hz
  have hz₁ : γ 1 ∈ (rectAB 1 1).side₂ := by rw [hpath.target]; exact hw
  have hS : ∃ z₀ ∈ (rectAB 1 1).side₁,
      lfppDOn ξ g (rectAB 1 1).toSet z₀ (pc e s₀) ≤
        ∫⁻ t in Icc 0 t₀, lenDens ξ f γ t := by
    rcases hstart with ⟨hmeet, hbefore⟩ | ⟨ht0, hside⟩
    · refine ⟨γ 0, hz₀, ?_⟩
      rw [show pc e s₀ = γ t₀ by exact hmeet.symm]
      exact dOn_piece_le hfg hpath le_rfl ht₀.1 ht₀.2 hbefore
    · refine ⟨ρ s₀, hside, ?_⟩
      exact dOn_self_le (hρsq s₀ hs₀).1 _
  have hE : ∃ z₁ ∈ (rectAB 1 1).side₂,
      lfppDOn ξ g (rectAB 1 1).toSet (pc e s₁) z₁ ≤
        ∫⁻ t in Icc t₁ 1, lenDens ξ f γ t := by
    rcases hend with ⟨hmeet, hafter⟩ | ⟨ht1, hside⟩
    · refine ⟨γ 1, hz₁, ?_⟩
      rw [show pc e s₁ = γ t₁ by exact hmeet.symm]
      exact dOn_piece_le hfg hpath ht₁.1 ht₁.2 le_rfl hafter
    · refine ⟨ρ s₁, hside, ?_⟩
      exact dOn_self_le (hρsq s₁ hs₁).1 _
  obtain ⟨z₀, hz₀', hS⟩ := hS
  obtain ⟨z₁, hz₁', hE⟩ := hE
  have hpc : ∀ j ∈ ({e} : Finset (Circle × ℂ)),
      IsPiecewiseC1Path (pc j) (pc j 0) (pc j 1) := by
    intro j hj
    exact hρ
  have hpcsq : ∀ j ∈ ({e} : Finset (Circle × ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1, pc j t ∈ (rectAB 1 1).toSet ∩ Fr := by
    intro j hj t ht
    exact hρsq t ht
  have hpcfin : ∀ j ∈ ({e} : Finset (Circle × ℂ)), lfppLen ξ f (pc j) ≠ ⊤ := by
    intro j hj
    exact hρfin
  have hconn : ∀ i ∈ ({e} : Finset (Circle × ℂ)),
      ∀ j ∈ ({e} : Finset (Circle × ℂ)),
      (meetGraph pc (({e} : Finset (Circle × ℂ)) : Set (Circle × ℂ))).Reachable i j := by
    intro i hi j hj
    simp only [Finset.mem_singleton] at hi hj
    subst i
    subst j
    exact SimpleGraph.Reachable.refl _
  have hbase := glue_le (ξ := ξ) hfg hγfin
    (R := {e}) (pc := pc) hpc hpcsq hpcfin hconn
    ht₀.1 htord ht₁.2 (Finset.mem_singleton_self e)
    (Finset.mem_singleton_self e) hs₀ hs₁
    hz₀' hz₁' hS hE
  simpa only [Finset.sum_singleton] using hbase

end SupercriticalLQGUniqueness.B2.DG20Conc
