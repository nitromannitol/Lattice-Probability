/- Geometric bounds for avoiding repeated constant blocks in an IID sequence. -/
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecificLimits.Basic

/-! Geometric bounds for avoiding repeated constant blocks in an IID sequence. -/
namespace LatticeProb.Prob.IidBlocks
open MeasureTheory ProbabilityTheory MeasurableSpace Filter
open scoped ENNReal
variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A constant word on the `n`th disjoint block of length `L`. -/
def constantBlock (a : A) (L n : ℕ) : Set (ℕ → A) :=
  {ω | ∀ i < L, ω (n * L + i) = a}

/-- None of the first `n` disjoint blocks is the specified constant word. -/
def avoidsConstantBlocks (a : A) (L n : ℕ) : Set (ℕ → A) :=
  {ω | ∀ j < n, ω ∉ constantBlock a L j}

private abbrev coordinateSpace (S : Set ℕ) : MeasurableSpace (ℕ → A) :=
  ⨆ i ∈ S, (inferInstance : MeasurableSpace A).comap (fun ω => ω i)

private theorem measurableSet_constantBlock_in (a : A) (L n : ℕ) (S : Set ℕ)
    (hS : ∀ i < L, n * L + i ∈ S) :
    MeasurableSet[coordinateSpace S] (constantBlock a L n) := by
  have hm : ∀ i < L, @Measurable (ℕ → A) A (coordinateSpace S) _
      (fun ω => ω (n * L + i)) := fun i hi =>
    measurable_iff_comap_le.mpr (le_iSup₂_of_le (n * L + i) (hS i hi) le_rfl)
  have h := MeasurableSet.iInter fun i => MeasurableSet.iInter fun (hi : i < L) =>
    (hm i hi) (measurableSet_singleton a)
  convert h using 1
  ext ω
  simp [constantBlock]

/-- The event specifying a constant word on a fixed finite coordinate block is measurable.

The complete public statement is
```lean
theorem measurableSet_constantBlock (a : A) (L n : ℕ) :
    MeasurableSet (constantBlock a L n)
```
-/
theorem measurableSet_constantBlock (a : A) (L n : ℕ) :
    MeasurableSet (constantBlock a L n) := by
  have h := MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < L) =>
    (measurable_pi_apply (n * L + i) : Measurable (fun ω : ℕ → A => ω (n * L + i)))
      (measurableSet_singleton a)
  convert h using 1
  ext ω
  simp [constantBlock]

/-- The event avoiding the given constant word on finitely many disjoint blocks is measurable.

The complete public statement is
```lean
theorem measurableSet_avoidsConstantBlocks (a : A) (L n : ℕ) :
    MeasurableSet (avoidsConstantBlocks a L n)
```
-/
theorem measurableSet_avoidsConstantBlocks (a : A) (L n : ℕ) :
    MeasurableSet (avoidsConstantBlocks a L n) := by
  have h := MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j < n) =>
    (measurableSet_constantBlock a L j).compl
  convert h using 1
  ext ω
  simp [avoidsConstantBlocks]

variable (μ : Measure A) [IsProbabilityMeasure μ]

/-- The exact mass of one constant block under the actual infinite product. -/
theorem measure_constantBlock (a : A) (L n : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ) (constantBlock a L n) = μ {a} ^ L := by
  classical
  have he : constantBlock a L n =
      Set.pi (Finset.Ico (n * L) (n * L + L)) (fun _ => {a}) := by
    ext ω
    constructor
    · intro h i hi
      have hi' := Finset.mem_Ico.mp hi
      have he : n * L + (i - n * L) = i := Nat.add_sub_of_le hi'.1
      have hj : i - n * L < L := by omega
      exact he ▸ h (i - n * L) hj
    · intro h i hi
      exact h (n * L + i) (Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩)
  rw [he, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton a)]
  simp

private theorem avoids_indep_block (a : A) (L n : ℕ) :
    IndepSet (avoidsConstantBlocks a L n) (constantBlock a L n)ᶜ
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
  let m : ℕ → MeasurableSpace (ℕ → A) := fun i =>
    (inferInstance : MeasurableSpace A).comap (fun ω => ω i)
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ℕ → A)) :=
    fun i => (measurable_pi_apply i).comap_le
  have hi : iIndep m (Measure.infinitePi (fun _ : ℕ => μ)) :=
    (iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)).iIndep
  have hd : Disjoint {i : ℕ | i < n * L} {i : ℕ | n * L ≤ i} :=
    Set.disjoint_left.mpr (fun _ h1 h2 => Nat.not_lt_of_ge h2 h1)
  apply (indep_iSup_of_disjoint hm hi hd).indepSet_of_measurableSet
  · have h := MeasurableSet.iInter fun j => MeasurableSet.iInter fun (hj : j < n) =>
      (measurableSet_constantBlock_in a L j {i | i < n * L} (by
        intro i hi'
        have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hj)
        dsimp
        rw [Nat.succ_mul] at hmul
        omega)).compl
    convert h using 1
    ext ω
    simp [avoidsConstantBlocks]
  · exact (measurableSet_constantBlock_in a L n {i | n * L ≤ i}
      (fun _ _ => Nat.le_add_right _ _)).compl

/-- Exact geometric avoidance mass; independence is derived from disjoint IID coordinates. -/
theorem measure_avoidsConstantBlocks (a : A) (L n : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ) (avoidsConstantBlocks a L n) =
      (1 - μ {a} ^ L) ^ n := by
  induction n with
  | zero => simp [avoidsConstantBlocks]
  | succ n ih =>
    have he : avoidsConstantBlocks a L (n + 1) =
        avoidsConstantBlocks a L n ∩ (constantBlock a L n)ᶜ := by
      ext ω
      simp only [avoidsConstantBlocks, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · intro h
        exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩
      · rintro ⟨h, hn⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h j hj
        · exact hn
    rw [he, (avoids_indep_block μ a L n).measure_inter_eq_mul, ih,
      prob_compl_eq_one_sub (measurableSet_constantBlock a L n),
      measure_constantBlock, pow_succ]

/-- **Measure equals zero of subset avoids constant blocks.** Any event forcing avoidance of every positive-mass block is null. -/
theorem measure_eq_zero_of_subset_avoidsConstantBlocks (a : A) (L : ℕ)
    (ha : μ {a} ≠ 0) (S : Set (ℕ → A))
    (hS : ∀ n, S ⊆ avoidsConstantBlocks a L n) :
    Measure.infinitePi (fun _ : ℕ => μ) S = 0 := by
  have hq : 1 - μ {a} ^ L < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (pow_ne_zero _ ha)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
  intro n
  rw [← measure_avoidsConstantBlocks μ a L n]
  exact measure_mono (hS n)
end LatticeProb.Prob.IidBlocks
