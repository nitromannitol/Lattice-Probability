/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorNoLog at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorFiber
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 


theorem laneC_separator_has_no_ratio_log
    {X : Set ℂ} (hX : IsCompact X) {c v : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hXann : ∀ z ∈ X, r < dist z c ∧ dist z c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r))) :
    ¬ QuantumZipper.CA.Topo.HasLogOn (fun z => (z - c) / (z - v)) X := by
  have hc : c ∉ X := by
    intro h
    have := (hXann c h).1
    simp only [dist_self] at this
    linarith
  have hvX : v ∉ X := by
    intro h
    have := (hXann v h).2
    linarith
  intro hlog
  have hcomp : v ∈ connectedComponentIn Xᶜ c :=
    QuantumZipper.CA.Topo.not_separates_of_hasLogOn hX hc hvX hlog
  have hpc : IsPathConnected (connectedComponentIn Xᶜ c) :=
    (hX.isClosed.isOpen_compl.connectedComponentIn.isConnected_iff_isPathConnected).1
      (isConnected_connectedComponentIn_iff.2 (by simpa using hc))
  obtain ⟨γ, hγ⟩ := hpc.joinedIn c (mem_connectedComponentIn (by simpa using hc))
    v hcomp
  have hsep' : LQGMetric.Disconnects X (closedBall c r) (ball c (2 * r))ᶜ :=
    LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep
  obtain ⟨z, ⟨t, rfl⟩, hzX⟩ := hsep' c v γ
    (by simp [hr.le])
    (by simpa only [mem_compl_iff, mem_ball, not_lt] using hv)
  exact connectedComponentIn_subset _ _ (hγ t) hzX

end SupercriticalLQGUniqueness.B2.DG20Conc
