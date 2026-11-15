import LatticeProb.MeasureTheory.MaximalAEProfileRun
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue

/-! # Bounded almost-everywhere constant runs -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

/-- A maximal almost-everywhere constant run in a bounded real interval has
finite endpoints and absorbs every overlapping constant open interval. -/
theorem exists_bounded_ae_profile_run
    {β : Type*} (f : ℝ → β) (c : β) (a b x : ℝ)
    (hx : ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧ V ⊆ Ioo a b ∧
      ∀ᵐ y ∂(volume.restrict V), f y = c) :
    ∃ l r : ℝ, a ≤ l ∧ l < x ∧ x < r ∧ r ≤ b ∧
      (∀ᵐ y ∂(volume.restrict (Ioo l r)), f y = c) ∧
      ∀ p q : ℝ, Ioo p q ⊆ Ioo a b →
        (Ioo l r ∩ Ioo p q).Nonempty → ∀ d : β,
        (∀ᵐ y ∂(volume.restrict (Ioo p q)), f y = d) →
        d = c ∧ Ioo p q ⊆ Ioo l r := by
  obtain ⟨C, hCopen, hCconn, hxC, hCsub, hCae, hmax⟩ :=
    exists_maximal_ae_profile_run volume (Ioo a b) f c x hx
  have hne : C.Nonempty := ⟨x, hxC⟩
  have hbelow : BddBelow C := ⟨a, fun t ht => (hCsub ht).1.le⟩
  have habove : BddAbove C := ⟨b, fun t ht => (hCsub ht).2.le⟩
  have hClower : a ≤ sInf C := le_csInf hne (fun t ht => (hCsub ht).1.le)
  have hCupper : sSup C ≤ b := csSup_le hne (fun t ht => (hCsub ht).2.le)
  have hCeq : C = Ioo (sInf C) (sSup C) := by
    apply Subset.antisymm
    · intro t ht
      obtain ⟨p, q, ⟨hp, hq⟩, hpq⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hCopen.mem_nhds ht)
      have hpC : (p + t) / 2 ∈ C := hpq ⟨by linarith, by linarith⟩
      have hqC : (t + q) / 2 ∈ C := hpq ⟨by linarith, by linarith⟩
      exact ⟨lt_of_le_of_lt (csInf_le hbelow hpC) (by linarith),
        lt_of_lt_of_le (by linarith) (le_csSup habove hqC)⟩
    · exact (show IsConnected C from ⟨hne, hCconn⟩).Ioo_csInf_csSup_subset hbelow habove
  rw [hCeq] at hxC hCae hmax
  refine ⟨sInf C, sSup C, hClower, hxC.1, hxC.2, hCupper, hCae, ?_⟩
  intro p q hpq hinter d hd
  exact hmax (Ioo p q) isOpen_Ioo isPreconnected_Ioo hpq hinter d hd

end LatticeProb
