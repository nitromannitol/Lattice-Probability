/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundPolarData at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.AroundFinite

 




set_option autoImplicit false
noncomputable section

open Set Metric TopologicalSpace

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem around_polar_data (A : EuclideanAnnulus) (j : Fin 4) :
    Bornology.IsBounded (Strong.cfgOpens A j : Set ℂ) ∧
    IsCompact (Strong.cfgSet₁ A j) ∧ IsCompact (Strong.cfgSet₂ A j) ∧
    IsConnected (Strong.cfgSet₁ A j) ∧ IsConnected (Strong.cfgSet₂ A j) ∧
    (Strong.cfgSet₁ A j).Nontrivial ∧ (Strong.cfgSet₂ A j).Nontrivial ∧
    Strong.cfgSet₁ A j ⊆ Strong.cfgOpens A j ∧
    Strong.cfgSet₂ A j ⊆ Strong.cfgOpens A j ∧
    Disjoint (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j) ∧
    IsConnected (Strong.cfgOpens A j : Set ℂ) := by
  have h := Strong.axiomV_data A.center (Strong.annL A) (Strong.annΔ A)
    (Strong.annΔ_pos A) j
  rcases h with ⟨_, hconn, hc₁, hc₂, hconn₁, hconn₂, hnt₁, hnt₂,
    hsub₁, hsub₂, hdisj⟩
  have hb : Bornology.IsBounded (Strong.cfgOpens A j : Set ℂ) :=
    (isBounded_closedBall (x := A.center) (r := A.outerRadius)).subset (by
      intro z hz
      have hmem := Strong.cfgOpens_subset_toSet A j hz
      rw [EuclideanAnnulus.toSet_eq] at hmem
      exact mem_closedBall.mpr hmem.2.le)
  exact ⟨hb, hc₁, hc₂, hconn₁, hconn₂, hnt₁, hnt₂, hsub₁, hsub₂,
    hdisj, hconn⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
