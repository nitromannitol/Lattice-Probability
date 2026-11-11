import Mathlib
import LatticeProb.Gauss.GFFCovPSD6
import LatticeProb.Gauss.GFFExistence

/-!
# Positive semidefiniteness of the whole-plane covariance (assembly)

`wholePlaneCovPSD_proved` proves the Prop `WholePlaneCovPSDStmt` (`LatticeProb.Gauss.GFFExistence`). For admissible observables `o_1, …, o_n` and reals `c_k`, put
`m = ∑_k c_k B_k` with `B_k` the mass of the representation of `o_k`, and add the unit circle `∂B_1(0)` with weight
`-m` (total mass zero: `-m · 1 + m = 0`). Then, with `A_k = L_{o_k}` (logarithmic potential), `V_{ij} = Λ(o_i, o_j)`
(logarithmic energy), `Cov = A B + B A - V` (`cov_eq`) and `Λ(circle, ·) = Λ(·, circle) = A` (Jensen):

  `∑_{ij} c_i c_j Cov_{ij} = 2 m ∑_k c_k A_k - ∑_{ij} c_i c_j V_{ij} = -∑_{I,J} d_I d_J Λ(I, J) ≥ 0`

by conditional negativity of the logarithmic energy on mass-zero measures (`sum_log_nonpos` in `LatticeProb.Gauss.GFFCovPSD5`).
-/

open MeasureTheory
open scoped Real

namespace LatticeProb.Gauss

open GFFCovPSD

/-- A smearing representation of every admissible observable. -/
noncomputable def admRep (o : GFFObservable.Admissible) : GFFCovPSD.SmearRep o.1 :=
  match o with
  | ⟨.pairing _φ, h⟩ => GFFCovPSD.pairingRep h
  | ⟨.circle _ _, h⟩ => GFFCovPSD.circleRep h

/-- The observables of the family: the unit circle at `none`, the observable `o k` at `some k`. -/
noncomputable def famObs {n : ℕ} (o : Fin n → GFFObservable.Admissible) : Option (Fin n) → GFFObservable
  | none => GFFObservable.circle 1 0
  | some k => (o k).1

/-- The representations of the family. -/
noncomputable def famRep {n : ℕ} (o : Fin n → GFFObservable.Admissible) :
    (i : Option (Fin n)) → GFFCovPSD.SmearRep (famObs o i)
  | none => GFFCovPSD.SmearRep.unitCircle
  | some k => admRep (o k)

/-- The weights of the family: `-m` on the unit circle, `c k` on `o k`. -/
def famWeight {n : ℕ} (c : Fin n → ℝ) (m : ℝ) : Option (Fin n) → ℝ
  | none => -m
  | some k => c k

lemma famRep_mass_none {n : ℕ} (o : Fin n → GFFObservable.Admissible) :
    (famRep o none).mass = 1 :=
  GFFCovPSD.SmearRep.unitCircle_mass

lemma famRep_logEnergy_none_left {n : ℕ} (o : Fin n → GFFObservable.Admissible) (j : Fin n) :
    (famRep o none).logEnergy (famRep o (some j)) = (famRep o (some j)).logPotential :=
  GFFCovPSD.SmearRep.logEnergy_unitCircle_left _

lemma famRep_logEnergy_none_right {n : ℕ} (o : Fin n → GFFObservable.Admissible) (i : Fin n) :
    (famRep o (some i)).logEnergy (famRep o none) = (famRep o (some i)).logPotential :=
  GFFCovPSD.SmearRep.logEnergy_unitCircle_right _

lemma famRep_logEnergy_none_self {n : ℕ} (o : Fin n → GFFObservable.Admissible) :
    (famRep o none).logEnergy (famRep o none) = 0 :=
  GFFCovPSD.SmearRep.logEnergy_unitCircle_self

/-- Algebra of the assembly: the sum of `c_i c_j (A_i B_j + B_i A_j - V_ij)` is `2 (∑ c A)(∑ c B) - ∑ c c V`. -/
lemma sum_cov_split {n : ℕ} (c A B : Fin n → ℝ) (V : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * (A i * B j + B i * A j - V i j)
      = 2 * (∑ i, c i * A i) * (∑ j, c j * B j) - ∑ i, ∑ j, c i * c j * V i j := by
  have e : ∀ i j, c i * c j * (A i * B j + B i * A j - V i j)
      = (c i * A i) * (c j * B j) + (c i * B i) * (c j * A j) - c i * c j * V i j := fun i j => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
  ring

/-- Expansion of the conditionally negative form on the family: `∑_{I,J} d_I d_J Λ(I,J) = -2 m ∑ c A + ∑ c c Λ`. -/
lemma family_sum_eq {n : ℕ} (o : Fin n → GFFObservable.Admissible) (c : Fin n → ℝ) (m : ℝ) :
    ∑ I, ∑ J, famWeight c m I * famWeight c m J * (famRep o I).logEnergy (famRep o J)
      = -2 * m * (∑ k, c k * (famRep o (some k)).logPotential)
        + ∑ i, ∑ j, c i * c j * (famRep o (some i)).logEnergy (famRep o (some j)) := by
  have hnone : ∑ J, famWeight c m none * famWeight c m J * (famRep o none).logEnergy (famRep o J)
      = -m * ∑ k, c k * (famRep o (some k)).logPotential := by
    rw [Fintype.sum_option]
    simp only [famWeight, famRep_logEnergy_none_self, famRep_logEnergy_none_left, mul_zero, zero_add]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsome : ∀ i : Fin n, ∑ J, famWeight c m (some i) * famWeight c m J
      * (famRep o (some i)).logEnergy (famRep o J)
      = c i * (-m * (famRep o (some i)).logPotential)
        + ∑ j, c i * c j * (famRep o (some i)).logEnergy (famRep o (some j)) := by
    intro i
    rw [Fintype.sum_option]
    simp only [famWeight, famRep_logEnergy_none_right]
    ring
  have hsum : ∑ i, c i * (-m * (famRep o (some i)).logPotential)
      = -m * ∑ k, c k * (famRep o (some k)).logPotential := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Fintype.sum_option, hnone]
  simp only [hsome]
  rw [Finset.sum_add_distrib, hsum]
  ring

/-- The whole-plane covariance is positive semidefinite (`LatticeProb.Gauss.WholePlaneCovPSDStmt`). -/
theorem wholePlaneCovPSD_proved : WholePlaneCovPSDStmt := by
  intro n o c
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∑ k, c k * (famRep o (some k)).mass := ⟨_, rfl⟩
  have hd : ∑ i, famWeight c m i * (famRep o i).mass = 0 := by
    rw [Fintype.sum_option]
    simp only [famWeight, famRep_mass_none, mul_one]
    rw [← hm]
    ring
  have key : ∑ I, ∑ J, famWeight c m I * famWeight c m J * (famRep o I).logEnergy (famRep o J) ≤ 0 :=
    GFFCovPSD.sum_log_nonpos (famRep o) (famWeight c m) hd
  rw [family_sum_eq] at key
  have hQ : ∑ i, ∑ j, c i * c j * wholePlaneGFFCov (o i).1 (o j).1
      = 2 * m * (∑ k, c k * (famRep o (some k)).logPotential)
        - ∑ i, ∑ j, c i * c j * (famRep o (some i)).logEnergy (famRep o (some j)) := by
    have hcov : ∀ i j, wholePlaneGFFCov (o i).1 (o j).1 = (famRep o (some i)).logPotential * (famRep o (some j)).mass
        + (famRep o (some i)).mass * (famRep o (some j)).logPotential - (famRep o (some i)).logEnergy (famRep o (some j)) :=
      fun i j => GFFCovPSD.SmearRep.cov_eq (famRep o (some i)) (famRep o (some j))
    simp only [hcov]
    rw [sum_cov_split, ← hm]
    ring
  linarith

end LatticeProb.Gauss
