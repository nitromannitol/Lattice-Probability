import LatticeProb.LQG.LocalHullFieldPhase

/-! # Measurable selection of locally gated field phases -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A phase selected from a countable family by a random-set-measurable index
is observable in the join of the locally gated phase sigma algebras. -/
theorem measurable_selected_localHullFieldPhase {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (n : ℕ) (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p)
    (f : Ω → ℕ) (hf : Measurable[setSigma A] f) :
    Measurable[⨆ k, localHullFieldSigma h A n (ψ k) hp]
      (fun ω => localHullFieldPhase h A n (ψ (f ω)) hp ω) := by
  let m : MeasurableSpace Ω := ⨆ k, localHullFieldSigma h A n (ψ k) hp
  let : MeasurableSpace Ω := m
  have hset : setSigma A ≤ m :=
    (le_sup_left : setSigma A ≤ hullSigma0 h A n).trans
      ((le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n (ψ 0) hp).trans
        (le_iSup (fun k => localHullFieldSigma h A n (ψ k) hp) 0))
  have hfm : Measurable f := hf.mono hset le_rfl
  have hphase (k : ℕ) : Measurable (localHullFieldPhase h A n (ψ k) hp) :=
    (comap_measurable _).mono
      ((le_sup_right : MeasurableSpace.comap (localHullFieldPhase h A n (ψ k) hp)
        inferInstance ≤ localHullFieldSigma h A n (ψ k) hp).trans
        (le_iSup (fun k => localHullFieldSigma h A n (ψ k) hp) k)) le_rfl
  intro s hs
  have heq : (fun ω => localHullFieldPhase h A n (ψ (f ω)) hp ω) ⁻¹' s =
      ⋃ k : ℕ, ({ω | f ω = k} ∩ (localHullFieldPhase h A n (ψ k) hp ⁻¹' s)) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨f ω, rfl, hω⟩
    · rintro ⟨k, hk, hω⟩
      simpa only [hk] using hω
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    ((measurableSet_singleton k).preimage hfm).inter (hphase k hs)

end LatticeProb.LQG
