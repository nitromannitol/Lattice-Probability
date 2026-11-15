/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ClockedWalkExitParameter at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   local import paths and one deprecated proof lemma name are updated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkStopping
import LatticeProb.Bonanno.BouRabeeGwynne.WalkExcursionRecovery

/-! A measurable choice of a vertex-exit parameter on a fixed pasted walk.
The choice uses only the countable data of cumulative integer durations and
the concatenated first-exit index, rather than a choice of an original path. -/

open MeasureTheory Set
open scoped unitInterval

namespace BouRabeeGwynne

abbrev WalkPrefixTimeData (n : ℕ) :=
  {t : Fin (n + 2) → ℕ // Monotone t ∧ t 0 = 0}

namespace WalkPrefixTimeData

variable {n : ℕ}

def duration (D : WalkPrefixTimeData n) : ℕ := D.val (Fin.last (n + 1))

noncomputable def knots (P : TimePartition n) (D : WalkPrefixTimeData n) : WeakTimeKnots n :=
  Classical.choose (exists_weakWalkTimeKnots P D.val D.property.1 D.property.2 rfl)

lemma knots_scaled (P : TimePartition n) (D : WalkPrefixTimeData n) (i : Fin (n + 2)) :
    (D.duration : ℝ) * ((D.knots P).knots i : ℝ) = (D.val i : ℝ) :=
  Classical.choose_spec
    (exists_weakWalkTimeKnots P D.val D.property.1 D.property.2 rfl) i

noncomputable def vertexTime (D : WalkPrefixTimeData n) (m : ℕ) : unitInterval :=
  ⟨(min m D.duration : ℕ) / (D.duration : ℝ), by
    by_cases hM : D.duration = 0
    · simp only [hM, Nat.cast_zero, div_zero]
      exact ⟨le_rfl, zero_le_one⟩
    have hMpos : (0 : ℝ) < D.duration := by exact_mod_cast Nat.pos_of_ne_zero hM
    exact ⟨div_nonneg (Nat.cast_nonneg _) hMpos.le,
      (div_le_one hMpos).mpr (by exact_mod_cast min_le_right m D.duration)⟩⟩

@[simp] lemma vertexTime_zero (D : WalkPrefixTimeData n) : D.vertexTime 0 = 0 := by
  apply Subtype.ext
  simp [vertexTime]

lemma vertexTime_scaled (D : WalkPrefixTimeData n) (m : ℕ) :
    (D.duration : ℝ) * (D.vertexTime m : ℝ) = (min m D.duration : ℕ) := by
  by_cases hM : D.duration = 0
  · simp [hM]
  change (D.duration : ℝ) * ((min m D.duration : ℕ) / (D.duration : ℝ)) = _
  rw [mul_comm, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hM)]

private lemma exists_preimage_vertexTime (P : TimePartition n) (D : WalkPrefixTimeData n)
    (m : ℕ) : ∃ a : unitInterval, P.weakClock (D.knots P) a = D.vertexTime m := by
  have hb : D.vertexTime m ∈ Icc (P.weakClock (D.knots P) 0) (P.weakClock (D.knots P) 1) := by
    rw [P.weakClock_zero, P.weakClock_one]
    exact (D.vertexTime m).property
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc
    (show (0 : unitInterval) ≤ 1 from zero_le_one)
    (P.weakClock (D.knots P)).continuous.continuousOn hb
  exact ⟨a, ha⟩

/-- The preimage is a fixed choice from countable integer data. At zero exit
the chosen parameter is explicitly zero. -/
noncomputable def exitParameter (P : TimePartition n) (D : WalkPrefixTimeData n)
    (m : ℕ) : unitInterval :=
  if m = 0 then 0 else Classical.choose (exists_preimage_vertexTime P D m)

@[simp] lemma exitParameter_zero (P : TimePartition n) (D : WalkPrefixTimeData n) :
    D.exitParameter P 0 = 0 := by simp [exitParameter]

lemma exitParameter_clock (P : TimePartition n) (D : WalkPrefixTimeData n) (m : ℕ) :
    P.weakClock (D.knots P) (D.exitParameter P m) = D.vertexTime m := by
  by_cases hm : m = 0
  · subst m
    rw [exitParameter_zero, vertexTime_zero, P.weakClock_zero]
  · simp only [exitParameter, ite_eq_right hm]
    exact Classical.choose_spec (exists_preimage_vertexTime P D m)

lemma measurable_exitParameter (P : TimePartition n) :
    Measurable (fun p : WalkPrefixTimeData n × ℕ => p.1.exitParameter P p.2) :=
  measurable_of_countable _

end WalkPrefixTimeData

namespace ClockedWalkExcursion

variable {d n : ℕ}

noncomputable def prefixTimes (e : ℕ → Bool × ClockedWalkExcursion d) : Fin (n + 2) → ℕ :=
  Fin.cases 0 (fun i => (concatenate (fun k => (e k).2) i.val).1)

lemma prefixTimes_monotone (e : ℕ → Bool × ClockedWalkExcursion d) :
    Monotone (prefixTimes (n := n) e) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact Nat.zero_le _
  · change (concatenate (fun j => (e j).2) k.val).1 ≤
      (concatenate (fun j => (e j).2) k.val).1 + (e (k.val + 1)).2.1
    exact Nat.le_add_right _ _

noncomputable def prefixTimeData (e : ℕ → Bool × ClockedWalkExcursion d) : WalkPrefixTimeData n :=
  ⟨prefixTimes e, prefixTimes_monotone e, rfl⟩

lemma measurable_prefixTimeData :
    Measurable (prefixTimeData (d := d) (n := n)) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact (measurable_concatenate j.val).fst.comp
      (Measurable.of_eval fun k => (measurable_pi_apply k).snd)

@[simp] lemma prefixTimeData_duration (e : ℕ → Bool × ClockedWalkExcursion d) :
    (prefixTimeData (n := n) e).duration = (concatenate (fun k => (e k).2) n).1 := rfl

noncomputable def concatenatedExitIndex (U : Set (Euc d))
    (e : ℕ → Bool × ClockedWalkExcursion d) : ℕ :=
  min ((FiniteConductanceNetwork.exitTime U (concatenate (fun k => (e k).2) n).2).untopD 0)
    (prefixTimeData (n := n) e).duration

lemma measurable_concatenatedExitIndex {U : Set (Euc d)} (hU : MeasurableSet U) :
    Measurable (concatenatedExitIndex (n := n) U) := by
  have hτ : Measurable (FiniteConductanceNetwork.exitTime U) :=
    (FiniteConductanceNetwork.coordinateProcess_adapted.isStoppingTime_hittingAfter hU.compl).measurable'
  have hc : Measurable (fun e : ℕ → Bool × ClockedWalkExcursion d =>
      concatenate (fun k => (e k).2) n) := (measurable_concatenate n).comp
    (Measurable.of_eval fun k => (measurable_pi_apply k).snd)
  exact ((hτ.comp hc.snd).untopD 0).min hc.fst

/-- Defined on every rich sequence. No compatible-sequence or original-path
witness is needed to define or measure this stopping parameter. -/
noncomputable def pastedVertexExitParameter (U : Set (Euc d)) (P : TimePartition n)
    (e : ℕ → Bool × ClockedWalkExcursion d) : unitInterval :=
  (prefixTimeData e).exitParameter P (concatenatedExitIndex (n := n) U e)

lemma measurable_pastedVertexExitParameter {U : Set (Euc d)} (hU : MeasurableSet U)
    (P : TimePartition n) : Measurable (pastedVertexExitParameter U P) :=
  (WalkPrefixTimeData.measurable_exitParameter P).comp
    (measurable_prefixTimeData.prodMk (measurable_concatenatedExitIndex (n := n) hU))

lemma pastedVertexExitParameter_clock (U : Set (Euc d)) (P : TimePartition n)
    (e : ℕ → Bool × ClockedWalkExcursion d) :
    P.weakClock ((prefixTimeData e).knots P) (pastedVertexExitParameter U P e) =
      (prefixTimeData (n := n) e).vertexTime (concatenatedExitIndex (n := n) U e) :=
  WalkPrefixTimeData.exitParameter_clock P _ _

end ClockedWalkExcursion
end BouRabeeGwynne
