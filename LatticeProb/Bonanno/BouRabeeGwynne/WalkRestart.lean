/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkRestart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DiscreteHarmonicMeasure
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling

/-! Exact discrete restart identities for the actual first vertex exit.
These pathwise identities retain the complete shifted path and the same exit
vertex, including a restart exactly at the exit time. -/

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*}

def walkShift (n : ℕ) (ω : ℕ → V) : ℕ → V := fun k => ω (n + k)

lemma measurable_walkShift [MeasurableSpace V] (n : ℕ) :
    Measurable (walkShift (V := V) n) :=
  Measurable.of_eval fun k => measurable_pi_apply (n + k)

@[simp] lemma walkShift_zero (ω : ℕ → V) : walkShift 0 ω = ω := by
  funext k
  simp [walkShift]

lemma walkShift_add (n m : ℕ) (ω : ℕ → V) :
    walkShift m (walkShift n ω) = walkShift (n + m) ω := by
  funext k
  simp [walkShift, Nat.add_assoc]

/-- Restarting before or at a finite first exit subtracts exactly the elapsed
number of steps from the canonical exit time. -/
lemma exitTime_walkShift_of_eq (A : Set V) (ω : ℕ → V) {τ n : ℕ}
    (hτ : exitTime A ω = (τ : WithTop ℕ)) (hn : n ≤ τ) :
    exitTime A (walkShift n ω) = ((τ - n : ℕ) : WithTop ℕ) := by
  have hterminal : ω τ ∉ A := by
    obtain ⟨j, hj, hbad⟩ := (exitTime_le_iff A ω τ).mp hτ.le
    have htj : τ ≤ j := by
      by_contra h
      have hlt : j < τ := Nat.lt_of_not_ge h
      apply hbad
      apply mem_of_lt_exitTime
      rw [hτ]
      exact_mod_cast hlt
    simpa only [Nat.le_antisymm hj htj] using hbad
  apply WithTop.eq_of_forall_le_coe_iff
  intro m
  constructor
  · intro hm
    obtain ⟨k, hkm, hbad⟩ := (exitTime_le_iff A (walkShift n ω) m).mp hm
    have hle : exitTime A ω ≤ ((n + k : ℕ) : WithTop ℕ) :=
      (exitTime_le_iff A ω (n + k)).mpr ⟨n + k, le_rfl, hbad⟩
    rw [hτ] at hle
    have ht : τ ≤ n + k := by exact_mod_cast hle
    have htm : τ - n ≤ m := by omega
    exact WithTop.coe_le_coe.mpr htm
  · intro hm
    have htm : τ - n ≤ m := WithTop.coe_le_coe.mp hm
    apply (exitTime_le_iff A (walkShift n ω) m).mpr
    refine ⟨τ - n, htm, ?_⟩
    simpa only [walkShift, Nat.add_sub_of_le hn] using hterminal

/-- The restarted full path exits at the very same vertex as the original. -/
lemma exitVertex_walkShift_of_eq (A : Set V) (ω : ℕ → V) {τ n : ℕ}
    (hτ : exitTime A ω = (τ : WithTop ℕ)) (hn : n ≤ τ) :
    exitVertex A (walkShift n ω) = exitVertex A ω := by
  simp only [exitVertex, exitTime_walkShift_of_eq A ω hτ hn, hτ, walkShift]
  change ω (n + (τ - n)) = ω τ
  rw [Nat.add_sub_of_le hn]

end BouRabeeGwynne.FiniteConductanceNetwork
