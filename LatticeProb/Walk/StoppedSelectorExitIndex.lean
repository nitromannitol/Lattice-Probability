import LatticeProb.Bonanno.BouRabeeGwynne.WalkReconstructionLaw

/-! # Target exit before a stopped selector stage -/

set_option autoImplicit false
noncomputable section

open Set Metric BouRabeeGwynne

namespace LatticeProb

/-- If a stopped selector lies outside a thickening of the target and two
vertex representatives are close, the first target exit precedes the stopped
stage. The stage is assumed finite and stopped. -/
theorem exists_exit_index_le_stopped_stage_of_close
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (p q : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → Euc d → Option J) (U : Set (Euc d))
    {a δ : ℝ} (haδ : a < δ) (hpq : ∀ v, dist (p v) (q v) ≤ a)
    (hnone : ∀ i x, select i x = none → x ∉ thickening δ U)
    (ω : ℕ → V) (n : ℕ)
    (hfinite : (FiniteConductanceNetwork.actualWalkStage q B initial
      (fun i v => select i (q v)) n ω).1 ≠ ⊤)
    (hstop : (FiniteConductanceNetwork.actualWalkStage q B initial
      (fun i v => select i (q v)) n ω).2.1 = true) :
    ∃ k : ℕ, k ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
      (fun i v => select i (q v)) n ω).1.untopD 0 ∧
      FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω = (k : WithTop ℕ) := by
  have hselect : ∀ i v, select i (q v) = none → v ∉ p ⁻¹' U := by
    intro i v hs hv
    apply hnone i (q v) hs
    exact Metric.mem_thickening_iff.mpr ⟨p v, hv, by
      rw [dist_comm]
      exact lt_of_le_of_lt (hpq v) haδ⟩
  have hle := FiniteConductanceNetwork.actualWalkStage_exit_le_of_stopped
    q B initial (fun i v => select i (q v)) (p ⁻¹' U) hselect ω n hfinite hstop
  have hexit : FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hle
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hexit
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hfinite
  refine ⟨k, ?_, hk.symm⟩
  rw [← hk, ← hl] at hle
  simpa only [← hl, WithTop.untopD_coe] using (WithTop.coe_le_coe.mp hle)

end LatticeProb
end
