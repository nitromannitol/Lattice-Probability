import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected

/-! # Simple connectivity of plane domains -/

open Set Metric Bornology

namespace LatticeProb.Topology

/-- A proper nonempty plane domain with only unbounded complementary components is simply connected. -/
theorem isSimplyConnected_of_unbounded_compl_components {U : Set ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty) (hproper : U ≠ univ)
    (hcomp : ∀ a ∉ U, ¬ IsBounded (connectedComponentIn Uᶜ a)) : IsSimplyConnected U := by
  obtain ⟨f, hf, hfd, g, hg, hgd, hgf⟩ :=
    QuantumZipper.CA.RMT.riemann_mapping_of_hasHoloSqrt hU hc hne hproper
      (QuantumZipper.CA.RMT.hasHoloSqrt_of_unbounded_compl hU hc hcomp)
  have hfg : ∀ y ∈ ball (0 : ℂ) 1, f (g y) = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hf.2.2 hy
    rw [hgf hx]
  let e : U ≃ₜ ball (0 : ℂ) 1 :=
    { toFun := fun x => ⟨f x, hf.1 x.property⟩
      invFun := fun y => ⟨g y, hg.1 y.property⟩
      left_inv := fun x => Subtype.ext (hgf x.property)
      right_inv := fun y => Subtype.ext (hfg y y.property)
      continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hfd.continuousOn).subtype_mk _
      continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp hgd.continuousOn).subtype_mk _ }
  let : ContractibleSpace (ball (0 : ℂ) 1) := contractibleSpace_ball (by norm_num)
  exact e.toHomotopyEquiv.simplyConnectedSpace

end LatticeProb.Topology
