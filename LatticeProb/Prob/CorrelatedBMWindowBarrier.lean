/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Prob.ContinuousPathClosedBarrier

/-! # Measurable barriers on increment windows

Continuous-path barriers and endpoint corrections are measurable using only
increment evaluations on the relevant closed windows. -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A continuous path barrier on a closed interval only needs the evaluations
inside that interval to be measurable. -/
theorem measurableSet_closedBarrier_of_local_evaluations {Ω : Type*}
    [MeasurableSpace Ω] (X : Ω → ℝ → ℝ) (Y : Ω → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hcont : ∀ ω, Continuous (X ω))
    (hX : ∀ t ∈ Icc a b, Measurable (fun ω => X ω t)) (hY : Measurable Y) :
    MeasurableSet {ω | ∀ t ∈ Icc a b, Y ω ≤ X ω t} := by
  have heq : {ω | ∀ t ∈ Icc a b, Y ω ≤ X ω t} =
      {ω | Y ω ≤ X ω a} ∩ {ω | Y ω ≤ X ω b} ∩
      {ω | ∀ q : ℚ, (q : ℝ) ∈ Ioo a b → Y ω ≤ X ω q} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨h a ⟨le_rfl, hab⟩, h b ⟨hab, le_rfl⟩⟩,
        fun q hq => h q ⟨hq.1.le, hq.2.le⟩⟩
    · rintro ⟨⟨ha, hb⟩, hq⟩ t ht
      rcases lt_or_eq_of_le ht.1 with hta | rfl
      · rcases lt_or_eq_of_le ht.2 with htb | rfl
        · by_contra hn
          have hopen : IsOpen (Ioo a b ∩ {s | X ω s < Y ω}) :=
            isOpen_Ioo.inter (isOpen_lt (hcont ω) continuous_const)
          obtain ⟨q, h⟩ := Rat.denseRange_cast.exists_mem_open hopen
            ⟨t, ⟨hta, htb⟩, lt_of_not_ge hn⟩
          exact (not_le_of_gt h.2) (hq q h.1)
        · exact hb
      · exact ha
  rw [heq]
  refine ((measurableSet_le hY (hX a ⟨le_rfl, hab⟩)).inter
    (measurableSet_le hY (hX b ⟨hab, le_rfl⟩))).inter ?_
  apply measurableSet_setOfPred.2
  apply Measurable.forall
  intro q
  by_cases hq : (q : ℝ) ∈ Ioo a b
  · exact measurable_const.imp (measurableSet_setOfPred.1
      (measurableSet_le hY (hX q ⟨hq.1.le, hq.2.le⟩)))
  · simp [hq]

namespace CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Lower barriers relative to either endpoint are measurable in the increment
process on a closed window. -/
theorem measurableSet_window_barrier (a b q : ℝ) (hab : a ≤ b) (i : Fin 2)
    (right : Bool) :
    MeasurableSet[MeasurableSpace.comap
      (fun ω : Path2 => fun (p : Fin 2 × {x : ℝ // x ∈ Icc a b}) =>
        coneIncr p.1 p.2.1 a ω) inferInstance]
      {ω | ∀ t ∈ Icc a b,
        q ≤ coneIncr i t a ω - if right then coneIncr i b a ω else 0} := by
  let W := fun ω : Path2 => fun (p : Fin 2 × {x : ℝ // x ∈ Icc a b}) =>
    coneIncr p.1 p.2.1 a ω
  let m := MeasurableSpace.comap W inferInstance
  let : MeasurableSpace Path2 := m
  have heval (t : ℝ) (ht : t ∈ Icc a b) :
      Measurable (fun ω : Path2 => coneIncr i t a ω) :=
    (measurable_pi_apply ((i, ⟨t, ht⟩) : Fin 2 × {x : ℝ // x ∈ Icc a b})).comp
      (comap_measurable W)
  apply measurableSet_closedBarrier_of_local_evaluations
    (fun ω t => coneIncr i t a ω - if right then coneIncr i b a ω else 0)
    (fun _ => q) hab
  · intro ω
    unfold coneIncr lrCoord
    split_ifs <;> fun_prop
  · intro t ht
    exact (heval t ht).sub (by cases right <;> simp [heval b ⟨hab, le_rfl⟩])
  · exact measurable_const

/-- Endpoint increments from two windows give a measurable correction in the
joint window sigma algebra. -/
theorem measurable_window_endpoint_correction (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (i : Fin 2) :
    Measurable[MeasurableSpace.comap
      (fun ω : Path2 =>
        ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc a b}) => coneIncr p.1 p.2.1 a ω),
         (fun (p : Fin 2 × {x : ℝ // x ∈ Icc c d}) => coneIncr p.1 p.2.1 c ω)))
      inferInstance] (fun ω => coneIncr i b a ω - coneIncr i d c ω) := by
  let W := fun ω : Path2 =>
    ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc a b}) => coneIncr p.1 p.2.1 a ω),
     (fun (p : Fin 2 × {x : ℝ // x ∈ Icc c d}) => coneIncr p.1 p.2.1 c ω))
  have hW : Measurable[MeasurableSpace.comap W inferInstance] W := comap_measurable W
  exact ((measurable_pi_apply (i, ⟨b, ⟨hab, le_rfl⟩⟩)).comp
    (measurable_fst.comp hW)).sub
      ((measurable_pi_apply (i, ⟨d, ⟨hcd, le_rfl⟩⟩)).comp
        (measurable_snd.comp hW))

/-- The sum of endpoint increments from two windows is measurable in their
joint window sigma algebra. -/
theorem measurable_window_endpoint_sum (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (i : Fin 2) :
    Measurable[MeasurableSpace.comap
      (fun ω : Path2 =>
        ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc a b}) => coneIncr p.1 p.2.1 a ω),
         (fun (p : Fin 2 × {x : ℝ // x ∈ Icc c d}) => coneIncr p.1 p.2.1 c ω)))
      inferInstance] (fun ω => coneIncr i b a ω + coneIncr i d c ω) := by
  let W := fun ω : Path2 =>
    ((fun (p : Fin 2 × {x : ℝ // x ∈ Icc a b}) => coneIncr p.1 p.2.1 a ω),
     (fun (p : Fin 2 × {x : ℝ // x ∈ Icc c d}) => coneIncr p.1 p.2.1 c ω))
  have hW : Measurable[MeasurableSpace.comap W inferInstance] W := comap_measurable W
  exact ((measurable_pi_apply (i, ⟨b, ⟨hab, le_rfl⟩⟩)).comp
    (measurable_fst.comp hW)).add
      ((measurable_pi_apply (i, ⟨d, ⟨hcd, le_rfl⟩⟩)).comp
        (measurable_snd.comp hW))

end CorrelatedBM
end LatticeProb
