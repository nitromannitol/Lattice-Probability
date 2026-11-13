/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.TopoLog at commit fdb5cad; only the module paths of local imports are changed. -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.BranchLogRoot
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg

/-! # Logarithms on simply connected planar domains

The logarithm supplied by the exponential covering map, restricted to a compact
separator, is the input to Eilenberg's criterion in `TopoEilenberg`.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic

open Set Complex QuantumZipper.CA.Topo

/-- Every point outside an open simply connected domain has a continuous
logarithm of the displacement map on the domain. -/
theorem topo_hasLogOn_sub_of_simplyConnected {D : Set ℂ} (hDo : IsOpen D)
    [SimplyConnectedSpace D] {a : ℂ} (ha : a ∉ D) :
    HasLogOn (fun z : ℂ => z - a) D := by
  have hDs : IsSimplyConnected D := (inferInstance : SimplyConnectedSpace D)
  have hnonzero : 0 ∉ (fun z : ℂ => z - a) '' D := by
    rintro ⟨z, hz, heq⟩
    exact ha (sub_eq_zero.mp heq ▸ hz)
  obtain ⟨L, hLc, hL⟩ := exists_continuousOn_eqOn_exp_comp hDs hDo
    (continuousOn_id.sub continuousOn_const) hnonzero
  exact ⟨L, hLc, fun z hz => hL hz⟩

/-- A ratio of two displacement maps has a logarithm on a simply connected domain. -/
theorem topo_hasLogOn_ratio_of_simplyConnected {D : Set ℂ} (hDo : IsOpen D)
    [SimplyConnectedSpace D] {a b : ℂ} (ha : a ∉ D) (hb : b ∉ D) :
    HasLogOn (fun z : ℂ => (z - a) / (z - b)) D := by
  obtain ⟨L₁, hL₁c, hL₁⟩ := topo_hasLogOn_sub_of_simplyConnected hDo ha
  obtain ⟨L₂, hL₂c, hL₂⟩ := topo_hasLogOn_sub_of_simplyConnected hDo hb
  refine ⟨fun z => L₁ z - L₂ z, hL₁c.sub hL₂c, fun z hz => ?_⟩
  rw [exp_sub, hL₁ z hz, hL₂ z hz]

end MatedCRTHarmonic
