import LatticeProb.ReflectedGMS.GMS.IndexedConductanceDistortion
import LatticeProb.ReflectedGMS.GMS.IndexedConductanceMeasurable
import LatticeProb.ReflectedGMS.GMS.RestrictedCodeSlots

/-! # Measurability of decoded conductance discrepancies -/

set_option autoImplicit false

open Set Topology

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- The conductance term of decoded configurations is the guarded code supremum. -/
theorem conductance_iSup_eq_indexedConductanceDiscrepancy
    (x y : RawCode) (hx : IsGoodCode x) (hy : IsGoodCode y) (r : ℝ)
    (f : Plane ≃ₜ Plane)
    (hf : ∀ C ∈ (decodeConfig x).restrict (Metric.ball 0 r),
      mapCell f C ∈ (decodeConfig y).restrict (Metric.ball 0 r)) :
    (⨆ (C ∈ (decodeConfig x).restrict (Metric.ball 0 r))
      (C' ∈ (decodeConfig x).restrict (Metric.ball 0 r))
      (_ : (decodeConfig x).Adj C C'),
      ENNReal.ofReal |(decodeConfig x).c C C' -
        (decodeConfig y).c (mapCell f C) (mapCell f C')|) =
      indexedConductanceDiscrepancy r x y (⟨f, f.continuous⟩ : C(Plane, Plane)) := by
  classical
  rw [conductance_iSup_eq_indexed (decodeConfig x) (decodeConfig y) r f
    (slotCell x) (slotCell y) (fun i => SlotNear 0 r (x.1 i))
    (fun j => SlotNear 0 r (y.1 j))
    (mem_decodeConfig_restrict_ball_iff x 0 r)
    (mem_decodeConfig_restrict_ball_iff y 0 r) hf]
  unfold indexedConductanceDiscrepancy
  refine iSup_congr fun i => iSup_congr fun i' => iSup_congr fun j =>
    iSup_congr fun j' => ?_
  simp only [iSup_and']
  by_cases h : SlotNear 0 r (x.1 i) ∧ SlotNear 0 r (x.1 i') ∧
      SlotNear 0 r (y.1 j) ∧ SlotNear 0 r (y.1 j') ∧
      mapCell f (slotCell x i) = slotCell y j ∧
      mapCell f (slotCell x i') = slotCell y j' ∧ 0 < x.2 i i'
  · have hguard := h
    obtain ⟨hi, hi', hj, hj', he, he', hp⟩ := hguard
    have hi0 := hi
    have hi0' := hi'
    have hj0 := hj
    have hj0' := hj'
    obtain ⟨K, hK, _⟩ := hi0
    obtain ⟨K', hK', _⟩ := hi0'
    obtain ⟨L, hL, _⟩ := hj0
    obtain ⟨L', hL', _⟩ := hj0'
    have ha : (decodeConfig x).Adj (slotCell x i) (slotCell x i') :=
      (hx.decodeConfig_adj_slot (by simp [hK]) (by simp [hK'])).2 hp
    simp only [iSup_pos (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from
      ⟨hi, hi', hj, hj', he, he', ha⟩)]
    split
    · rw [slotCell_of_eq_some hK, slotCell_of_eq_some hK',
        slotCell_of_eq_some hL, slotCell_of_eq_some hL',
        hx.decodeConfig_c hK hK', hy.decodeConfig_c hL hL']
    · rename_i hnot
      exact (hnot ⟨hi, hi', hj, hj', he, he', hp⟩).elim
  · have ha : ¬ (SlotNear 0 r (x.1 i) ∧ SlotNear 0 r (x.1 i') ∧
        SlotNear 0 r (y.1 j) ∧ SlotNear 0 r (y.1 j') ∧
        mapCell f (slotCell x i) = slotCell y j ∧
        mapCell f (slotCell x i') = slotCell y j' ∧
        (decodeConfig x).Adj (slotCell x i) (slotCell x i')) := by
      rintro ⟨hi, hi', hj, hj', he, he', hadj⟩
      exact h ⟨hi, hi', hj, hj', he, he',
        (hx.decodeConfig_adj_slot ((slotNear_iff_isSome_inter_ball x 0 r i).1 hi).1
          ((slotNear_iff_isSome_inter_ball x 0 r i').1 hi').1).1 hadj⟩
    rw [iSup_neg ha]
    split
    · rename_i hg
      obtain ⟨hi, hi', hj, hj', he, he', hp⟩ := hg
      exact (h ⟨hi, hi', hj, hj', he, he', hp⟩).elim
    · rfl

/-- A measurable family of good codes has a measurable decoded conductance term. -/
theorem measurable_decoded_conductance_iSup
    {Ω : Type*} [MeasurableSpace Ω] (r : Ω → ℝ) (x y : Ω → RawCode)
    (f : Ω → Plane ≃ₜ Plane)
    (hr : Measurable r) (hx : Measurable x) (hy : Measurable y)
    (hf : Measurable fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)))
    (hgx : ∀ ω, IsGoodCode (x ω)) (hgy : ∀ ω, IsGoodCode (y ω))
    (hforward : ∀ ω C, C ∈ (decodeConfig (x ω)).restrict (Metric.ball 0 (r ω)) →
      mapCell (f ω) C ∈ (decodeConfig (y ω)).restrict (Metric.ball 0 (r ω))) :
    Measurable fun ω =>
      ⨆ (C ∈ (decodeConfig (x ω)).restrict (Metric.ball 0 (r ω)))
        (C' ∈ (decodeConfig (x ω)).restrict (Metric.ball 0 (r ω)))
        (_ : (decodeConfig (x ω)).Adj C C'),
        ENNReal.ofReal |(decodeConfig (x ω)).c C C' -
          (decodeConfig (y ω)).c (mapCell (f ω) C) (mapCell (f ω) C')| := by
  convert measurable_indexedConductanceDiscrepancy r x y
    (fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane))) hr hx hy hf using 1
  ext ω
  exact conductance_iSup_eq_indexedConductanceDiscrepancy _ _ (hgx ω) (hgy ω)
    _ _ (hforward ω)

end ReflectedGMS.GMS.ValidCodeSet
