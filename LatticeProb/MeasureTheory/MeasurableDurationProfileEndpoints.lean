import LatticeProb.MeasureTheory.MeasurableLocalProfileValue
import LatticeProb.MeasureTheory.MeasurableProfileRunEndpoints
import LatticeProb.MeasureTheory.MeasurableGridEndpoints
import LatticeProb.MeasureTheory.BoundedAEProfileRun
import LatticeProb.MeasureTheory.FiniteAbsorbedIntervalCover
import LatticeProb.MeasureTheory.FiniteIntervalAlignment

/-! # Measurable endpoint recovery from duration profiles -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

/-- A jointly measurable duration profile determines a measurable endpoint selector.
Recovery holds for an interval containing the anchor in a bounded almost-everywhere
cover by intervals with disjoint interiors. -/
theorem exists_measurable_duration_profile_endpoints
    {Θ : Type*} [MeasurableSpace Θ] (a u b : ℝ)
    (F : Θ × ℝ → ℝ) (hF : Measurable F) :
    ∃ E : Θ → ℝ × ℝ, Measurable E ∧
      ∀ (θ : Θ) {ι : Type*} (A B : ι → ℝ),
        (∀ i, a ≤ A i ∧ A i < B i ∧ B i ≤ b) →
        (Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j))) →
        volume (Ioo a b \ ⋃ i, Ioo (A i) (B i)) = 0 →
        (∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (A i) (B i))), F (θ, t) = B i - A i) →
        ∀ i, u ∈ Ioo (A i) (B i) → E θ = (A i, B i) := by
  classical
  obtain ⟨V, hV, hVeq⟩ := exists_measurable_local_profile_value u F hF
  obtain ⟨R, hR, hReq⟩ := exists_measurable_profile_run_endpoints a u b F hF
  obtain ⟨E, hE, hEeq⟩ := exists_measurable_grid_endpoints u (fun θ => (R θ).1) V
    hR.fst hV
  refine ⟨E, hE, ?_⟩
  intro θ ι A B hAB hdis hcover hprofile i hi
  have hsub : ∀ k, Ioo (A k) (B k) ⊆ Ioo a b := fun k =>
    Ioo_subset_Ioo (hAB k).1 (hAB k).2.2
  have hlen : 0 < B i - A i := sub_pos.mpr (hAB i).2.1
  have hvalue : V θ = B i - A i := hVeq θ (A i) (B i) (B i - A i)
    hi.1 hi.2 hlen.le (hprofile i)
  obtain ⟨l, r, hal, hlu, hur, hrb, hrun, hmax⟩ :=
    exists_bounded_ae_profile_run (fun t => F (θ, t)) (B i - A i) a b u
      ⟨Ioo (A i) (B i), isOpen_Ioo, hi, hsub i, hprofile i⟩
  have hr : R θ = (l, r) := hReq θ l r (B i - A i) hal hlu hur hrb hrun
    (fun p q hpq hinter d hd => (hmax p q hpq hinter d hd).2)
  have habs : ∀ k, (Ioo l r ∩ Ioo (A k) (B k)).Nonempty →
      Ioo (A k) (B k) ⊆ Ioo l r ∧ B k - A k = B i - A i := by
    intro k hk
    obtain ⟨heq, hsub'⟩ := hmax (A k) (B k) (hsub k) hk _ (hprofile k)
    exact ⟨hsub', heq⟩
  let S : Set ι := {k | (Ioo l r ∩ Ioo (A k) (B k)).Nonempty}
  obtain ⟨hfin, hbounds, _, hclosed⟩ := finite_cover_of_absorbed_intervals a b l r
    (B i - A i) A B hal (lt_trans hlu hur) hrb hlen (fun k => (hAB k).2.1)
    hdis hcover habs
  let : Finite S := hfin.to_subtype
  have hiS : i ∈ S := ⟨u, ⟨hlu, hur⟩, hi⟩
  obtain ⟨n, hn⟩ := interval_left_endpoint_eq_grid_point l r (B i - A i)
    (fun k : S => A k) (fun k : S => B k) hlen
    (fun k => (hbounds k k.property).1) (fun k => (hbounds k k.property).2.2)
    (fun k m hkm => hdis (fun h => hkm (Subtype.ext h))) hclosed
    ⟨i, hiS⟩ (hbounds i hiS).2.1
  have hleft : l + (n : ℝ) * (B i - A i) ≤ u := by linarith [hi.1]
  have hright : u < l + ((n : ℝ) + 1) * (B i - A i) := by nlinarith [hi.2]
  have hresult := hEeq θ (n : ℤ) (by simpa [hvalue] using hlen)
    (by simpa [hr, hvalue] using hleft) (by simpa [hr, hvalue] using hright)
  rw [hr, hvalue] at hresult
  simp only [Int.cast_natCast] at hresult
  rw [hresult]
  apply Prod.ext
  · exact hn.symm
  · dsimp
    nlinarith [hn]

end LatticeProb
