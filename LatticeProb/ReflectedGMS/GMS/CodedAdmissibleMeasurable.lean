import LatticeProb.ReflectedGMS.GMS.AdmissibleIndexed
import LatticeProb.ReflectedGMS.GMS.RestrictedCodeSlots
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedMeasurable
import LatticeProb.Topology.CompactImageMatching
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Measurability of coded cell admissibility -/

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace ReflectedGMS.GMS

open Code ValidCodeSet

noncomputable local instance : MeasurableSpace Cell := borel _
local instance : BorelSpace Cell := ⟨rfl⟩

/-- Exact image matching is measurable for measurable maps and compact cells. -/
private theorem measurableSet_plane_compact_image_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → C(Plane, Plane)) (K L : Ω → NonemptyCompacts Plane)
    (hF : Measurable F) (hK : Measurable K) (hL : Measurable L) :
    MeasurableSet {ω | (K ω).map (F ω) (F ω).continuous = L ω} := by
  let S : Set (C(Plane, Plane) × NonemptyCompacts Plane × NonemptyCompacts Plane) :=
    {p | p.2.1.map p.1 p.1.continuous = p.2.2}
  have hS : IsClosed S := by
    exact LatticeProb.isClosed_nonemptyCompacts_image_eq Prod.fst (fun p : C(Plane, Plane) × NonemptyCompacts Plane × NonemptyCompacts Plane => p.2.1)
      (fun p => p.2.2) continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)
  exact hS.measurableSet.preimage (hF.prodMk (hK.prodMk hL))

/-- The active cells of a countable family can be matched measurably to another family. -/
private theorem measurableSet_plane_forall_exists_compact_image_eq
    {Ω I J : Type*} [MeasurableSpace Ω] [Countable I] [Countable J]
    (F : Ω → C(Plane, Plane)) (K : I → Ω → NonemptyCompacts Plane)
    (L : J → Ω → NonemptyCompacts Plane) (A : I → Set Ω) (B : J → Set Ω)
    (hF : Measurable F) (hK : ∀ i, Measurable (K i))
    (hL : ∀ j, Measurable (L j)) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ j, MeasurableSet (B j)) :
    MeasurableSet {ω | ∀ i, ω ∈ A i → ∃ j, ω ∈ B j ∧
      (K i ω).map (F ω) (F ω).continuous = L j ω} := by
  apply measurableSet_setOfPred.2
  exact Measurable.forall fun i => (measurableSet_setOfPred.1 (hA i)).imp <|
    Measurable.exists fun j => (measurableSet_setOfPred.1 (hB j)).and <|
      measurableSet_setOfPred.1 (measurableSet_plane_compact_image_eq F (K i) (L j) hF (hK i) (hL j))


/-- Adjacency preservation under all active image matches is a measurable event. -/
private theorem measurableSet_plane_forall_compact_image_adj
    {Ω I J : Type*} [MeasurableSpace Ω] [Countable I] [Countable J]
    (F : Ω → C(Plane, Plane)) (K : I → Ω → NonemptyCompacts Plane)
    (L : J → Ω → NonemptyCompacts Plane) (A : I → Set Ω) (B : J → Set Ω)
    (E : I → I → Set Ω) (D : J → J → Set Ω)
    (hF : Measurable F) (hK : ∀ i, Measurable (K i))
    (hL : ∀ j, Measurable (L j)) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ j, MeasurableSet (B j))
    (hE : ∀ i i', MeasurableSet (E i i')) (hD : ∀ j j', MeasurableSet (D j j')) :
    MeasurableSet {ω | ∀ i i' j j',
      ω ∈ A i → ω ∈ A i' → ω ∈ B j → ω ∈ B j' →
      (K i ω).map (F ω) (F ω).continuous = L j ω →
      (K i' ω).map (F ω) (F ω).continuous = L j' ω →
      ω ∈ E i i' → ω ∈ D j j'} := by
  apply measurableSet_setOfPred.2
  refine Measurable.forall fun i => Measurable.forall fun i' =>
    Measurable.forall fun j => Measurable.forall fun j' => ?_
  exact (measurableSet_setOfPred.1 (hA i)).imp <|
    (measurableSet_setOfPred.1 (hA i')).imp <|
    (measurableSet_setOfPred.1 (hB j)).imp <|
    (measurableSet_setOfPred.1 (hB j')).imp <|
    (measurableSet_setOfPred.1
      (measurableSet_plane_compact_image_eq F (K i) (L j) hF (hK i) (hL j))).imp <|
    (measurableSet_setOfPred.1
      (measurableSet_plane_compact_image_eq F (K i') (L j') hF (hK i') (hL j'))).imp <|
    (measurableSet_setOfPred.1 (hE i i')).imp (measurableSet_setOfPred.1 (hD j j'))


/-- Fixed-radius admissibility is measurable for good codes and a measurable pair of
forward and inverse continuous maps. -/
theorem measurableSet_admissibleAt_decodeConfig
    {Ω : Type*} [MeasurableSpace Ω] (r : ℝ)
    (x y : Ω → RawCode) (f : Ω → (Plane ≃ₜ Plane))
    (hx : Measurable x) (hy : Measurable y)
    (hgoodx : ∀ ω, IsGoodCode (x ω)) (hgoody : ∀ ω, IsGoodCode (y ω))
    (hf : Measurable fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)))
    (hfi : Measurable fun ω => (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane))) :
    MeasurableSet {ω | CellConfig.AdmissibleAt (decodeConfig (x ω))
      (decodeConfig (y ω)) r (f ω)} := by
  let K : ℕ → Ω → Cell := fun n ω => slotCell (x ω) n
  let L : ℕ → Ω → Cell := fun n ω => slotCell (y ω) n
  let A : ℕ → Set Ω := fun n => {ω | SlotNear 0 r ((x ω).1 n)}
  let B : ℕ → Set Ω := fun n => {ω | SlotNear 0 r ((y ω).1 n)}
  let E : ℕ → ℕ → Set Ω := fun n m => {ω | 0 < (x ω).2 n m}
  let D : ℕ → ℕ → Set Ω := fun n m => {ω | 0 < (y ω).2 n m}
  have hK : ∀ n, Measurable (K n) := fun n => (measurable_slotCell n).comp hx
  have hL : ∀ n, Measurable (L n) := fun n => (measurable_slotCell n).comp hy
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_setOfPred.2 ((measurable_slotNear 0 r n).comp hx)
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_setOfPred.2 ((measurable_slotNear 0 r n).comp hy)
  have hE : ∀ n m, MeasurableSet (E n m) := fun n m =>
    measurableSet_lt measurable_const ((measurable_rawCond n m).comp hx)
  have hD : ∀ n m, MeasurableSet (D n m) := fun n m =>
    measurableSet_lt measurable_const ((measurable_rawCond n m).comp hy)
  have hfor := measurableSet_plane_forall_exists_compact_image_eq
    (fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane))) K L A B hf hK hL hA hB
  have hback := measurableSet_plane_forall_exists_compact_image_eq
    (fun ω => (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane))) L K B A hfi hL hK hB hA
  have hadj := measurableSet_plane_forall_compact_image_adj
    (fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane))) K L A B E D hf hK hL hA hB hE hD
  have hadj' := measurableSet_plane_forall_compact_image_adj
    (fun ω => (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane))) L K B A D E hfi hL hK hB hA hD hE
  have heq : {ω | CellConfig.AdmissibleAt (decodeConfig (x ω))
      (decodeConfig (y ω)) r (f ω)} =
      {ω | (∀ i, ω ∈ A i → ∃ j, ω ∈ B j ∧
          (K i ω).map (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)) (f ω).continuous = L j ω) ∧
        (∀ j, ω ∈ B j → ∃ i, ω ∈ A i ∧
          (L j ω).map (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane)) (f ω).symm.continuous = K i ω) ∧
        (∀ i i' j j', ω ∈ A i → ω ∈ A i' → ω ∈ B j → ω ∈ B j' →
          (K i ω).map (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)) (f ω).continuous = L j ω →
          (K i' ω).map (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)) (f ω).continuous = L j' ω →
          ω ∈ E i i' → ω ∈ D j j') ∧
        (∀ j j' i i', ω ∈ B j → ω ∈ B j' → ω ∈ A i → ω ∈ A i' →
          (L j ω).map (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane)) (f ω).symm.continuous = K i ω →
          (L j' ω).map (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane)) (f ω).symm.continuous = K i' ω →
          ω ∈ D j j' → ω ∈ E i i')} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [CellConfig.admissibleAt_iff_indexed _ _ _ _ (fun n => K n ω)
      (fun n => L n ω) (fun n => ω ∈ A n) (fun n => ω ∈ B n)]
    · simp only [CellConfig.mapCell]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, ?_, ?_⟩
      · intro i i' j j' hi hi' hj hj' he he' ha
        exact (hgoody ω).decodeConfig_adj_slot
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj).1)
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj').1) |>.1
          (h3 i i' j j' hi hi' hj hj' he he'
            ((hgoodx ω).decodeConfig_adj_slot
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi).1)
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi').1) |>.2 ha))
      · intro j j' i i' hj hj' hi hi' he he' ha
        exact (hgoodx ω).decodeConfig_adj_slot
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi).1)
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi').1) |>.1
          (h4 j j' i i' hj hj' hi hi' he he'
            ((hgoody ω).decodeConfig_adj_slot
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj).1)
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj').1) |>.2 ha))
      · intro i i' j j' hi hi' hj hj' he he' ha
        exact (hgoody ω).decodeConfig_adj_slot
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj).1)
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj').1) |>.2
          (h3 i i' j j' hi hi' hj hj' he he'
            ((hgoodx ω).decodeConfig_adj_slot
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi).1)
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi').1) |>.1 ha))
      · intro j j' i i' hj hj' hi hi' he he' ha
        exact (hgoodx ω).decodeConfig_adj_slot
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi).1)
          (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hi').1) |>.2
          (h4 j j' i i' hj hj' hi hi' he he'
            ((hgoody ω).decodeConfig_adj_slot
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj).1)
              (((slotNear_iff_isSome_inter_ball _ _ _ _).1 hj').1) |>.1 ha))
    · intro C
      exact mem_decodeConfig_restrict_ball_iff (x ω) 0 r C
    · intro C
      exact mem_decodeConfig_restrict_ball_iff (y ω) 0 r C
  rw [heq]
  exact hfor.inter (hback.inter (hadj.inter hadj'))

end ReflectedGMS.GMS
