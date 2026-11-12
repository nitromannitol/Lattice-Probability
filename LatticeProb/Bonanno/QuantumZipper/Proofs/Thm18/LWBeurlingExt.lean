/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingExt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingDefs
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-4, B4b: local normal form of the cut-off of the extension by zero

We prove `ExtLocalFormStmt` (see `LWBeurlingDefs.lean` and `handoff/LW-BEURLING.md`).

Own elementary point-set topology argument (no published source needed; cost rule of
`AGENT_GUIDE.md`). Let `Vc = connectedComponentIn (D ∩ B(w, ρ)) w`, an open set. For
`x ∈ B(w, ρ)`:
* `x ∈ Vc`: on the open set `Vc` the function is `φ ∘ h = φ ∘ Re f` near `x`;
* `x ∉ closure Vc`: the indicator vanishes near `x`, and `φ 0 = 0`;
* `x ∈ closure Vc \ Vc`: then `x ∈ ∂D` (if `x ∈ D`, a small ball around `x` lies in
  `D ∩ B(w, ρ)`, is preconnected and meets `Vc`, hence lies in `Vc`), so by the decay
  hypothesis the indicator is `≤ ε` near `x` and `φ` of it vanishes.
-/

noncomputable section

open Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- **B4b** (own elementary proof): the cut-off `φ ∘ (1_{Vc} h)` has the local normal form
`LocConvHarmForm` on `B(w, ρ)`. -/
theorem extLocalFormStmt_holds : ExtLocalFormStmt := by
  intro D w ρ ε h φ hD hε hφ hφ0 hφ'' hharm hdecay x hxB
  set S : Set ℂ := D ∩ ball w ρ with hS
  set Vc : Set ℂ := connectedComponentIn S w with hVc
  have hSo : IsOpen S := hD.inter isOpen_ball
  have hVo : IsOpen Vc := hSo.connectedComponentIn
  have hVS : Vc ⊆ S := connectedComponentIn_subset S w
  by_cases hx : x ∈ Vc
  · obtain ⟨f, hf, hfeq⟩ := hharm x hx
    right
    refine ⟨φ, f, hφ, hφ'', hf, ?_⟩
    filter_upwards [hVo.mem_nhds hx, hfeq] with y hy1 hy2
    simp only [Set.indicator_of_mem hy1, hy2]
  left
  by_cases hc : x ∈ closure Vc
  · -- `x ∈ ∂D`
    have hxD : x ∉ D := by
      intro hxD
      obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hSo x ⟨hxD, hxB⟩
      obtain ⟨y, hyV, hxy⟩ := Metric.mem_closure_iff.mp hc r hr
      have hyball : y ∈ ball x r := by rw [mem_ball, dist_comm]; exact hxy
      have hsub : ball x r ⊆ connectedComponentIn S y :=
        (convex_ball x r).isPreconnected.subset_connectedComponentIn hyball hrS
      rw [← connectedComponentIn_eq hyV] at hsub
      exact hx (hsub (mem_ball_self hr))
    have hxfr : x ∈ frontier D := by
      rw [hD.frontier_eq]
      exact ⟨closure_mono (fun z hz => (hVS hz).1) hc, hxD⟩
    obtain ⟨δ, hδ, hδh⟩ := hdecay x ⟨hxfr, hxB⟩ ε hε
    filter_upwards [ball_mem_nhds x hδ] with y hy
    apply hφ0
    by_cases hyV : y ∈ Vc
    · rw [Set.indicator_of_mem hyV]
      exact hδh y hyV (mem_ball.mp hy)
    · rw [Set.indicator_of_notMem hyV]
      exact hε.le
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    have hyV : y ∉ Vc := fun h' => hy (subset_closure h')
    simp only [Set.indicator_of_notMem hyV]
    exact hφ0 0 hε.le

end LWFar
end Thm18Asm
end QuantumZipper
