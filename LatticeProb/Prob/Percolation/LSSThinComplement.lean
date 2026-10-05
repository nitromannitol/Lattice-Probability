/-
# The thin-form complement bridge for the Liggett--Schonmann--Stacey input

The Liggett--Schonmann--Stacey domination theorem has two dual halves on a `{0,1}`-field.  The
*dense* (lower-domination) half says that a sufficiently dense finite-range dependent field
stochastically dominates a product Bernoulli field on increasing events; the *thin*
(upper-domination) half says that a sufficiently thin field is stochastically dominated by a
product Bernoulli field on increasing events.  The dense half is proved elsewhere
(`Exploding.xlse_lss_general`, `Exploding/Support/ExtLSSCountable.lean`); this module proves the
**deterministic bridge** from that half to the thin half, with the dense domination entering
only as an explicit hypothesis on the complement field.

The bridge is the bit complement of the field.  Complementing a field of density `p` gives a
field of density `1 - p`; complementing an increasing event gives a decreasing one; the
parameter arithmetic is `1 - 7/8 = 1/8`.  The module proves every deterministic ingredient:

* the carrier map `bitCompl`, its involution law, and its measurability;
* the complement image of an increasing set is decreasing (and conversely);
* transport of `KDependent` across the carrier map (independence is preserved by the
  coordinatewise complement);
* the one-site probability complement relation `μ {ω s = false} = 1 - μ {ω s = true}` and the
  complement-field transport `(μ.map bitCompl) {ω s = true} = μ {ω s = false}`;
* the bit-level Bernoulli complement `(bernoulli p).map not = bernoulli (1 - p)` and the product
  field complement law `(bitProduct p).map bitCompl = bitProduct (1 - p)`;
* the measure-complement inequality: dense domination on increasing events bounds every
  decreasing set from above;
* the parameter arithmetic `1 - 7/8 = 1/8`.

No `Prop` is frozen, no cited statement is assumed, and `Rotor.External.LSS` is not claimed.
-/

import LatticeProb.Prob.Percolation.BondPercolation
import LatticeProb.Prob.Strassen.Defs
import LatticeProb.Site

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

variable {S : Type}

/-! ### The carrier map: the bit complement -/

/-- The coordinatewise bit complement of a `{0,1}`-field. -/
def bitCompl (ω : S → Bool) : S → Bool := fun s => !ω s

@[simp] theorem bitCompl_apply (ω : S → Bool) (s : S) : bitCompl ω s = !ω s := rfl

/-- The bit complement is an involution. -/
@[simp] theorem bitCompl_involutive (ω : S → Bool) : bitCompl (bitCompl ω) = ω := by
  funext s; simp [bitCompl]

theorem measurable_bool_not : Measurable (fun b : Bool => !b) :=
  fun _ _ => MeasurableSet.of_discrete

theorem measurable_bitCompl : Measurable (bitCompl : (S → Bool) → (S → Bool)) := by
  refine measurable_pi_lambda _ fun s => ?_
  exact measurable_bool_not.comp (measurable_pi_apply s)

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

theorem measurableSet_bitCompl_image {A : Set (S → Bool)} (hA : MeasurableSet A) :
    MeasurableSet (bitCompl '' A) := by
  rw [bitCompl_image_eq_preimage]
  exact hA.preimage measurable_bitCompl

/-! ### Increasing and decreasing events -/

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

/-! ### The dependent-field predicate and its transport -/

/-- A field law is `k`-dependent when bits at two finite index sets separated by more than `k`
in some coordinate are independent.  This is the finite-range dependence of the Liggett--
Schonmann--Stacey statement on the lattice `ℤ^d`. -/
def KDependent {d : ℕ} (k : ℕ) (μ : Measure (LatticeProb.Site d → Bool)) : Prop :=
  ∀ I J : Finset (LatticeProb.Site d),
    (∀ a ∈ I, ∀ b ∈ J, ∃ l : Fin d, (k : ℤ) < |a l - b l|) →
    IndepFun (fun ω : LatticeProb.Site d → Bool => fun i : I => ω i)
      (fun ω => fun j : J => ω j) μ

theorem measurable_finsetRestrict {d : ℕ} (I : Finset (LatticeProb.Site d)) :
    Measurable (fun ω : LatticeProb.Site d → Bool => fun i : I => ω i) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : LatticeProb.Site d)

theorem measurable_finsetCompl {d : ℕ} (I : Finset (LatticeProb.Site d)) :
    Measurable (fun f : I → Bool => fun i : I => !(f i)) :=
  measurable_pi_lambda _ fun i => measurable_bool_not.comp (measurable_pi_apply i)

/-- Independence transfers across a measurable carrier map: `X` and `Y` are independent under
`μ.map T` exactly when their pullbacks are independent under `μ`. -/
theorem indepFun_map_iff_of_measurable {α β Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    {T : Ω → Ω'} (hT : Measurable T) {X : Ω' → α} {Y : Ω' → β}
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    IndepFun X Y (μ.map T) ↔ IndepFun (X ∘ T) (Y ∘ T) μ := by
  have hXT : Measurable (X ∘ T) := hX.comp hT
  have hYT : Measurable (Y ∘ T) := hY.comp hT
  haveI : IsFiniteMeasure (μ.map T) := by infer_instance
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    indepFun_iff_map_prod_eq_prod_map_map hXT.aemeasurable hYT.aemeasurable,
    Measure.map_map (hX.prod hY) hT, Measure.map_map hX hT, Measure.map_map hY hT]
  rfl

/-- **`KDependent` transports across the carrier map.**  A `k`-dependent field remains
`k`-dependent after complementing every bit, because complementing bits is a measurable
coordinatewise bijection and independence is preserved by it. -/
theorem kDependent_map_bitCompl {d : ℕ} (k : ℕ) {μ : Measure (LatticeProb.Site d → Bool)}
    [IsFiniteMeasure μ] (h : KDependent k μ) : KDependent k (μ.map bitCompl) := by
  intro I J hfar
  have h' := h I J hfar
  refine (indepFun_map_iff_of_measurable (T := bitCompl) measurable_bitCompl
    (measurable_finsetRestrict I) (measurable_finsetRestrict J) μ).mpr ?_
  have := h'.comp (measurable_finsetCompl I) (measurable_finsetCompl J)
  exact this

/-! ### The complement field of a single site -/

/-- The complement field exchanges the one-site events `ω s = true` and `ω s = false`. -/
theorem compl_map_oneSite {d : ℕ} (μ : Measure (LatticeProb.Site d → Bool)) (s : LatticeProb.Site d) :
    (μ.map bitCompl) {ω | ω s = true} = μ {ω | ω s = false} := by
  have hs : MeasurableSet {ω : LatticeProb.Site d → Bool | ω s = true} := by
    have h : {ω : LatticeProb.Site d → Bool | ω s = true} =
        (fun f : LatticeProb.Site d → Bool => f s) ⁻¹' ({true} : Set Bool) := by
      ext ω; simp
    rw [h]
    exact (measurable_pi_apply s) (measurableSet_singleton true)
  rw [Measure.map_apply measurable_bitCompl hs]
  congr 1
  ext ω
  simp [bitCompl]

/-- The one-site probabilities of a probability law sum to one. -/
theorem compl_oneSite_eq_one_sub {d : ℕ} (μ : Measure (LatticeProb.Site d → Bool))
    [IsProbabilityMeasure μ] (s : LatticeProb.Site d) :
    μ {ω | ω s = false} = 1 - μ {ω | ω s = true} := by
  have hs : MeasurableSet {ω : LatticeProb.Site d → Bool | ω s = true} := by
    have h : {ω : LatticeProb.Site d → Bool | ω s = true} =
        (fun f : LatticeProb.Site d → Bool => f s) ⁻¹' ({true} : Set Bool) := by
      ext ω; simp
    rw [h]
    exact (measurable_pi_apply s) (measurableSet_singleton true)
  have h : {ω : LatticeProb.Site d → Bool | ω s = false} = {ω | ω s = true}ᶜ := by
    ext ω; simp
  rw [h, prob_compl_eq_one_sub hs]

/-! ### The product Bernoulli field and its complement law -/

/-- The product Bernoulli field on `S → Bool` of density `p`.  For the lattice carrier
`S = Site d` this is the product field the LSS statements are stated over. -/
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

/-! ### The dense-to-decreasing step and the bridge -/

/-- The dense (lower-domination) statement at the field `B` and the field law `ν`. -/
def DenseLower (B ν : Measure (S → Bool)) : Prop :=
  ∀ C : Set (S → Bool), MeasurableSet C → StrassenAux.IsIncreasingSet C → B C ≤ ν C

/-- The thin (upper-domination) statement at the field `B` and the field law `μ`. -/
def ThinUpper (B μ : Measure (S → Bool)) : Prop :=
  ∀ A : Set (S → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A → μ A ≤ B A

/-- **Dense domination bounds every DECREASING set from above.**  The complement of a decreasing
set is increasing, and the probabilities of complementary events sum to one. -/
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

/-- **The complement bridge.**  If a probability measure `ν` dominates the field `B` on
increasing events, `μ` is the field whose bit complement has law `ν`, and `B` and `B'` are
complementary fields (`B.map bitCompl = B'`), then `μ` is dominated by `B'` on increasing
events. -/
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

/-- **The thin form from the dense form, at complementary parameters.** -/
theorem thinUpper_bitProduct_compl {ρ : NNReal} (hρ : ρ ≤ 1) {ν μ : Measure (S → Bool)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : μ.map bitCompl = ν) (hdense : DenseLower (bitProduct ρ hρ S) ν) :
    ThinUpper (bitProduct (1 - ρ) tsub_le_self S) μ :=
  thinUpper_of_denseLower_compl (bitProduct_map_bitCompl (S := S) ρ hρ) hν hdense

/-- **The thin form at `1/8` from the dense form at `7/8`.**  The parameter arithmetic is the
complement `1 - 7/8 = 1/8`. -/
theorem thinUpper_eighth_of_dense_seven_eighths {ν μ : Measure (S → Bool)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hν : μ.map bitCompl = ν)
    (hdense : DenseLower (bitProduct (7 / 8) seven_eighths_le_one S) ν) :
    ThinUpper (bitProduct (1 / 8) one_eighth_le_one S) μ := by
  simpa only [one_sub_seven_eighths] using
    (thinUpper_bitProduct_compl (S := S) (ρ := 7 / 8) seven_eighths_le_one hν hdense)

/-- **The deterministic bridge, parameterised by the exact transported dense-domination
hypothesis.**  The hypothesis `hdense` is the dense (lower-domination) statement on the lattice
carrier, as supplied by the dense LSS half; applied to the complement field it yields the thin
(upper-domination) statement for the original field at the complementary parameter `1/8`.  The
dependence and density preconditions of the dense statement are met on the complement field by
`kDependent_map_bitCompl` and `compl_map_oneSite`. -/
theorem thinUpper_of_transported_dense {d : ℕ} (p : ℝ)
    (hdense : ∀ ν : Measure (LatticeProb.Site d → Bool), IsProbabilityMeasure ν →
      KDependent 2 ν →
      (∀ s : LatticeProb.Site d, ENNReal.ofReal p ≤ ν {ω | ω s = true}) →
      DenseLower (bitProduct (7 / 8) seven_eighths_le_one (LatticeProb.Site d)) ν)
    {μ : Measure (LatticeProb.Site d → Bool)} [IsProbabilityMeasure μ]
    (hKD : KDependent 2 μ)
    (hsite : ∀ s : LatticeProb.Site d, ENNReal.ofReal p ≤ μ {ω | ω s = false}) :
    ThinUpper (bitProduct (1 / 8) one_eighth_le_one (LatticeProb.Site d)) μ := by
  haveI : IsProbabilityMeasure (μ.map bitCompl) :=
    Measure.isProbabilityMeasure_map measurable_bitCompl.aemeasurable
  have hKDν : KDependent 2 (μ.map bitCompl) := kDependent_map_bitCompl 2 hKD
  have hsiteν : ∀ s : LatticeProb.Site d,
      ENNReal.ofReal p ≤ (μ.map bitCompl) {ω | ω s = true} := by
    intro s
    rw [compl_map_oneSite]
    exact hsite s
  have hd : DenseLower (bitProduct (7 / 8) seven_eighths_le_one (LatticeProb.Site d))
      (μ.map bitCompl) :=
    hdense (μ.map bitCompl) inferInstance hKDν hsiteν
  exact thinUpper_eighth_of_dense_seven_eighths (S := LatticeProb.Site d) rfl hd

end LatticeProb.Percolation
