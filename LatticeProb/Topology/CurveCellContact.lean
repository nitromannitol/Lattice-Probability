import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Contacts of curve segments -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Two continuously varying compact curve segments meet on a Borel set of parameters.
Each segment is parameterized linearly, so either endpoint order and degenerate segments
are allowed. -/
theorem measurableSet_curve_segment_contact
    {Ω E : Type} [MetricSpace E] [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (η : Ω → C(ℝ, E)) (a b c d : Ω → ℝ)
    (hη : Continuous η) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) :
    MeasurableSet {ω | ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      η ω (a ω + u * (b ω - a ω)) = η ω (c ω + v * (d ω - c ω))} := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let D : Ω → (ℝ × ℝ) → ℝ := fun ω p =>
    dist (η ω (a ω + p.1 * (b ω - a ω))) (η ω (c ω + p.2 * (d ω - c ω)))
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  have hD : Continuous (fun p : Ω × (ℝ × ℝ) => D p.1 p.2) := by
    dsimp [D]
    fun_prop
  have hmin : Continuous (fun ω => sInf (D ω '' K)) := hK.continuous_sInf hD
  have hEq : {ω | ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
      η ω (a ω + u * (b ω - a ω)) = η ω (c ω + v * (d ω - c ω))} =
      {ω | sInf (D ω '' K) = 0} := by
    ext ω
    have hcomp : IsCompact (D ω '' K) := hK.image (hD.comp (continuous_const.prodMk continuous_id))
    have hne : (D ω '' K).Nonempty := hKne.image _
    have hnonneg : 0 ≤ sInf (D ω '' K) := by
      apply le_csInf hne
      rintro x ⟨p, hp, rfl⟩
      exact dist_nonneg
    constructor
    · rintro ⟨u, hu, v, hv, heq⟩
      apply le_antisymm _ hnonneg
      have : D ω (u, v) = 0 := by
        dsimp [D]
        exact dist_eq_zero.mpr heq
      rw [← this]
      exact csInf_le hcomp.bddBelow ⟨(u, v), ⟨hu, hv⟩, rfl⟩
    · intro hzero
      obtain ⟨p, hp, hdist⟩ := hcomp.sInf_mem hne
      have heq : D ω p = 0 := by rw [hdist, hzero]
      exact ⟨p.1, hp.1, p.2, hp.2, dist_eq_zero.mp (by simpa only [D] using heq)⟩
  rw [hEq]
  exact (isClosed_singleton.preimage hmin).measurableSet

end LatticeProb
