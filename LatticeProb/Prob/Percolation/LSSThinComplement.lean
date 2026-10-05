/-
# The thin-form complement bridge for the Liggett--Schonmann--Stacey input

The Liggett--Schonmann--Stacey domination theorem has two dual halves.  On a `{0,1}`-field
indexed by a set `S`, the *dense* (lower-domination) half says that a sufficiently dense
`k`-dependent field stochastically dominates a product Bernoulli field of some density `ρ < 1`
on increasing events.  The *thin* (upper-domination) half says that a sufficiently thin field is
stochastically dominated by a product Bernoulli field of some small density on increasing events.
The two halves are related by complementing every bit of the field: complementing a field of
density `p` gives a field of density `1 - p`, and complementing an increasing event gives a
decreasing one.

This module proves that relation in the library's own vocabulary.  It does **not** prove either
LSS half: the dense hypothesis enters as an explicit argument of the theorems.  What is proved is
the complement bridge — the fact that the dense half, applied to the complement field at density
`7/8`, yields the thin half for the original field at density `1/8` — together with the bit-level
ingredients: the complement is an order-reversing involution, the complement of an increasing
event is decreasing, and the bit complement of a Bernoulli law is the Bernoulli law of the
complementary parameter.  No `Prop` is frozen here and no cited domination statement is assumed.
-/

import LatticeProb.Prob.Percolation.BondPercolation
import LatticeProb.Prob.Strassen.Defs

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Percolation

variable {S : Type}

/-! ### The bit complement and its order reversal -/

/-- The coordinatewise bit complement of a `{0,1}`-field. -/
def bitCompl (ω : S → Bool) : S → Bool := fun s => !ω s

@[simp] theorem bitCompl_apply (ω : S → Bool) (s : S) : bitCompl ω s = !ω s := rfl

/-- The bit complement is an involution. -/
@[simp] theorem bitCompl_involutive (ω : S → Bool) : bitCompl (bitCompl ω) = ω := by
  funext s; simp [bitCompl]

/-- The coordinatewise order on `{0,1}`-fields: every bit set in `x` is set in `y`. -/
def leField (x y : S → Bool) : Prop := ∀ s, x s = true → y s = true

/-- `IsIncreasingSet` is the `leField`-form of being closed under increasing a field. -/
theorem isIncreasingSet_iff_leField (A : Set (S → Bool)) :
    StrassenAux.IsIncreasingSet A ↔ ∀ x y, x ∈ A → leField x y → y ∈ A :=
  Iff.rfl

/-- A set is decreasing when it is closed under decreasing a field coordinatewise. -/
def IsDecreasingSet (A : Set (S → Bool)) : Prop :=
  ∀ x y : S → Bool, x ∈ A → leField y x → y ∈ A

/-- The complement of an increasing set is decreasing. -/
theorem isDecreasingSet_bitCompl_image {A : Set (S → Bool)}
    (hA : StrassenAux.IsIncreasingSet A) : IsDecreasingSet (bitCompl '' A) := by
  intro x y hx hle
  rw [isIncreasingSet_iff_leField] at hA
  rcases hx with ⟨a, ha, rfl⟩
  refine ⟨bitCompl y, ?_, by simp⟩
  refine hA a (bitCompl y) ha ?_
  intro s hs
  rw [bitCompl_apply]
  cases hy : y s with
  | false => rfl
  | true =>
      have hc : (bitCompl a) s = true := hle s hy
      rw [bitCompl_apply, hs] at hc
      exact absurd hc (by simp)

/-- The complement of a decreasing set is increasing. -/
theorem isIncreasingSet_compl {D : Set (S → Bool)} (hD : IsDecreasingSet D) :
    StrassenAux.IsIncreasingSet Dᶜ := by
  intro x y hx hle
  exact fun hy => hx (hD y x hy hle)

/-- Membership in the complement image is membership in the preimage under the involution. -/
theorem bitCompl_image_eq_preimage (A : Set (S → Bool)) :
    bitCompl '' A = bitCompl ⁻¹' A := by
  ext ω
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨bitCompl ω, by simpa using h, by simp⟩

/-- The complement image of the complement image is the original set. -/
theorem bitCompl_image_image (A : Set (S → Bool)) : bitCompl '' (bitCompl '' A) = A := by
  ext ω
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    simpa using hb
  · intro h
    exact ⟨bitCompl ω, ⟨ω, h, rfl⟩, by simp⟩

/-- The preimage of the complement image is the original set. -/
theorem bitCompl_preimage_image (A : Set (S → Bool)) : bitCompl ⁻¹' (bitCompl '' A) = A := by
  rw [← bitCompl_image_eq_preimage]
  exact bitCompl_image_image A

/-- The bit complement is measurable, the measurable space on `Bool` being discrete. -/
theorem measurable_bool_not : Measurable (fun b : Bool => !b) :=
  fun _ _ => MeasurableSet.of_discrete

theorem measurable_bitCompl : Measurable (bitCompl : (S → Bool) → (S → Bool)) := by
  refine measurable_pi_lambda _ fun s => ?_
  exact measurable_bool_not.comp (measurable_pi_apply s)

theorem measurableSet_bitCompl_image {A : Set (S → Bool)} (hA : MeasurableSet A) :
    MeasurableSet (bitCompl '' A) := by
  rw [bitCompl_image_eq_preimage]
  exact hA.preimage measurable_bitCompl

/-! ### The dense-to-decreasing step -/

/-- The dense (lower-domination) statement at the field `B` and the field law `ν`. -/
def DenseLower (B ν : Measure (S → Bool)) : Prop :=
  ∀ C : Set (S → Bool), MeasurableSet C → StrassenAux.IsIncreasingSet C → B C ≤ ν C

/-- The thin (upper-domination) statement at the field `B` and the field law `μ`. -/
def ThinUpper (B μ : Measure (S → Bool)) : Prop :=
  ∀ A : Set (S → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A → μ A ≤ B A

/-- **Dense domination bounds every DECREASING set from above.**  If a probability measure `ν`
dominates `Q` on increasing sets, then on decreasing sets `Q` bounds `ν` from above: the
complement of a decreasing set is increasing, and the probabilities of complementary events sum
to one. -/
theorem le_of_dense_of_isDecreasing {Q ν : Measure (S → Bool)} [IsProbabilityMeasure Q]
    [IsProbabilityMeasure ν] (hdense : DenseLower Q ν) :
    ∀ D : Set (S → Bool), MeasurableSet D → IsDecreasingSet D → ν D ≤ Q D := by
  intro D hD hdec
  have hDc : MeasurableSet Dᶜ := hD.compl
  have hinc : StrassenAux.IsIncreasingSet Dᶜ := isIncreasingSet_compl hdec
  have hle : Q Dᶜ ≤ ν Dᶜ := hdense Dᶜ hDc hinc
  calc ν D = ν (Dᶜ)ᶜ := by rw [compl_compl]
    _ = 1 - ν Dᶜ := prob_compl_eq_one_sub hDc
    _ ≤ 1 - Q Dᶜ := tsub_le_tsub_left hle 1
    _ = Q (Dᶜ)ᶜ := (prob_compl_eq_one_sub hDc).symm
    _ = Q D := by rw [compl_compl]

/-! ### The complement bridge -/

/-- **The complement bridge.**  If a probability measure `ν` dominates the field `B` on
increasing events (`B` might be a product field), and `μ` is the field whose bit complement has
law `ν`, and `B` and `B'` are complementary fields (`B.map bitCompl = B'`), then `μ` is dominated
by `B'` on increasing events.  This is the abstract form; the concrete product fields are
`bitProduct` below. -/
theorem thinUpper_of_denseLower_compl {B B' ν μ : Measure (S → Bool)}
    [IsProbabilityMeasure B] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hB : B.map bitCompl = B') (hν : μ.map bitCompl = ν) (hdense : DenseLower B ν) :
    ThinUpper B' μ := by
  intro A hAmeas hAinc
  have hDmeas : MeasurableSet (bitCompl '' A) := measurableSet_bitCompl_image hAmeas
  have hDdec : IsDecreasingSet (bitCompl '' A) := isDecreasingSet_bitCompl_image hAinc
  have hupper : ν (bitCompl '' A) ≤ B (bitCompl '' A) :=
    le_of_dense_of_isDecreasing hdense (bitCompl '' A) hDmeas hDdec
  have hνA : ν (bitCompl '' A) = μ A := by
    rw [← hν, Measure.map_apply measurable_bitCompl hDmeas, bitCompl_preimage_image]
  have hBA : B (bitCompl '' A) = B' A := by
    rw [← hB, Measure.map_apply measurable_bitCompl hAmeas, bitCompl_image_eq_preimage]
  calc μ A = ν (bitCompl '' A) := hνA.symm
    _ ≤ B (bitCompl '' A) := hupper
    _ = B' A := hBA

/-! ### The concrete Bernoulli product field -/

/-- The product Bernoulli field on `S → Bool` of density `p`.  For `S = Sym2 Site` this is
`bondLaw p`; it is the field the LSS producers are stated over. -/
noncomputable def bitProduct (p : NNReal) (hp : p ≤ 1) (S : Type*) : Measure (S → Bool) :=
  Measure.infinitePi (fun _ : S => bernoulli p hp)

instance bitProduct.instIsProbabilityMeasure (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bitProduct p hp S) := by
  unfold bitProduct; infer_instance

theorem seven_eighths_le_one : (7 / 8 : NNReal) ≤ 1 := by
  change ((7 / 8 : NNReal) : ℝ) ≤ 1
  norm_num

theorem one_eighth_le_one : (1 / 8 : NNReal) ≤ 1 := by
  change ((1 / 8 : NNReal) : ℝ) ≤ 1
  norm_num

theorem one_sub_seven_eighths : (1 : NNReal) - 7 / 8 = 1 / 8 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub seven_eighths_le_one]
  push_cast
  norm_num

set_option linter.deprecated false in
/-- **Complementing the bits of a Bernoulli law complements its parameter.** -/
theorem bernoulli_map_not (p : NNReal) (hp : p ≤ 1) :
    (bernoulli p hp).map (fun b : Bool => !b) = bernoulli (1 - p) tsub_le_self := by
  refine Measure.ext_of_singleton fun b => ?_
  have hm : Measurable (fun b : Bool => !b) := measurable_bool_not
  cases b with
  | false =>
      rw [Measure.map_apply hm MeasurableSet.of_discrete]
      have hpre : (fun b : Bool => !b) ⁻¹' ({false} : Set Bool) = {true} := by
        ext c; cases c <;> simp
      rw [hpre, bernoulli, bernoulli,
        PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.bernoulli_apply (p := p) hp,
        PMF.bernoulli_apply (p := 1 - p) tsub_le_self]
      simp only [Bool.cond_true, Bool.cond_false]
      rw [tsub_tsub_cancel_of_le hp]
  | true =>
      rw [Measure.map_apply hm MeasurableSet.of_discrete]
      have hpre : (fun b : Bool => !b) ⁻¹' ({true} : Set Bool) = {false} := by
        ext c; cases c <;> simp
      rw [hpre, bernoulli, bernoulli,
        PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        PMF.bernoulli_apply (p := p) hp,
        PMF.bernoulli_apply (p := 1 - p) tsub_le_self]
      simp only [Bool.cond_true, Bool.cond_false]

/-- **The product Bernoulli field is complemented by complementing its parameter.** -/
theorem bitProduct_map_bitCompl (p : NNReal) (hp : p ≤ 1) :
    (bitProduct p hp S).map bitCompl = bitProduct (1 - p) tsub_le_self S := by
  have h : (Measure.infinitePi (fun _ : S => bernoulli p hp)).map bitCompl
      = Measure.infinitePi (fun _ : S => (bernoulli p hp).map (fun b : Bool => !b)) := by
    rw [show bitCompl = (fun x : S → Bool => fun i : S => !(x i)) from rfl]
    exact Measure.infinitePi_map_pi (μ := fun _ : S => bernoulli p hp)
      (f := fun _ : S => fun b : Bool => !b) (fun _ => measurable_bool_not)
  rw [bitProduct, h, bernoulli_map_not]
  rfl

/-- **The thin form from the dense form, at complementary parameters.**  If a probability
measure `ν` dominates the product Bernoulli field of density `ρ` on increasing events, and `μ`
is the field whose bit complement has law `ν`, then `μ` is dominated by the product Bernoulli
field of density `1 - ρ` on increasing events. -/
theorem thinUpper_bitProduct_compl {ρ : NNReal} (hρ : ρ ≤ 1) {ν μ : Measure (S → Bool)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : μ.map bitCompl = ν) (hdense : DenseLower (bitProduct ρ hρ S) ν) :
    ThinUpper (bitProduct (1 - ρ) tsub_le_self S) μ :=
  thinUpper_of_denseLower_compl (bitProduct_map_bitCompl (S := S) ρ hρ) hν hdense

/-- **The thin form at `1/8` from the dense form at `7/8`.**  The parameter arithmetic is the
complement `1 - 7/8 = 1/8`; this is the form in which the rotor repository uses the thin LSS
input, with one-site probability at most `2ε` small and dominating Bernoulli `1/8`. -/
theorem thinUpper_eighth_of_dense_seven_eighths {ν μ : Measure (S → Bool)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : μ.map bitCompl = ν)
    (hdense : DenseLower (bitProduct (7 / 8) seven_eighths_le_one S) ν) :
    ThinUpper (bitProduct (1 / 8) one_eighth_le_one S) μ := by
  simpa only [one_sub_seven_eighths] using
    (thinUpper_bitProduct_compl (S := S) (ρ := 7 / 8) seven_eighths_le_one hν hdense)

end LatticeProb.Percolation
