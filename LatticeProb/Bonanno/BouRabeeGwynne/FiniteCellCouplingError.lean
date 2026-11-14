/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FiniteCellCouplingError at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.FinitePartitionCoupling
import Mathlib.Tactic.Linarith

/-! The continuous-cell mass errors bound the failure probability of the
explicit full-excursion coupling. Only the second law needs to give total
mass one to the chosen cells. -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace BouRabeeGwynne

/-- Once both marginals have terminated, their full joint law is concentrated
on the pair of constant states, independently of any later cell labels. -/
lemma coupling_bad_zero_of_dirac_marginals
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (ρ : Measure (X × Y)) {x : X} {y : Y}
    (hfst : ρ.fst = Measure.dirac x) (hsnd : ρ.snd = Measure.dirac y)
    {B : Set (X × Y)} (hB : (x, y) ∉ B) : ρ B = 0 := by
  have hx : ρ (Prod.fst ⁻¹' ({x}ᶜ : Set X)) = 0 := by
    rw [← Measure.fst_apply (measurableSet_singleton x).compl, hfst]
    simp
  have hy : ρ (Prod.snd ⁻¹' ({y}ᶜ : Set Y)) = 0 := by
    rw [← Measure.snd_apply (measurableSet_singleton y).compl, hsnd]
    simp
  apply measure_mono_null (t := Prod.fst ⁻¹' ({x}ᶜ : Set X) ∪
    Prod.snd ⁻¹' ({y}ᶜ : Set Y)) _ (measure_union_null hx hy)
  intro p hp
  by_cases hpx : p.1 = x
  · right
    change p.2 ∉ ({y} : Set Y)
    intro hpy
    exact hB (by simpa only [← hpx, ← Set.mem_singleton_iff.mp hpy] using hp)
  · left
    exact hpx

lemma commonCellDeficit_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) (hb : ∀ i, b i ≠ ⊤)
    (hsum : ∑ i, b i = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ i, |(a i).toReal - (b i).toReal| ≤ ε) :
    1 - ∑ i, min (a i) (b i) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
  have hab (i : ι) : b i ≤ a i + ENNReal.ofReal ε := by
    apply (ENNReal.toReal_le_toReal (hb i)
      (ENNReal.add_ne_top.mpr ⟨ha i, ENNReal.ofReal_ne_top⟩)).mp
    rw [ENNReal.toReal_add (ha i) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε]
    have he := (abs_le.mp (herror i)).1
    linarith
  have hm (i : ι) : b i ≤ min (a i) (b i) + ENNReal.ofReal ε := by
    by_cases hi : a i ≤ b i
    · rw [min_eq_left hi]
      exact hab i
    · rw [min_eq_right (le_of_not_ge hi)]
      exact le_self_add
  have hs : 1 ≤ (∑ i, min (a i) (b i)) +
      ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
    calc
      1 = ∑ i, b i := hsum.symm
      _ ≤ ∑ i, (min (a i) (b i) + ENNReal.ofReal ε) :=
        Finset.sum_le_sum (fun i _ => hm i)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp [ENNReal.ofReal_mul, nsmul_eq_mul]
  exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hs)

theorem finitePartitionCoupling_bad_le_of_cell_error
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : ι → Set X} {F : ι → Set Y}
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (hdE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hdF : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ν (⋃ i, F i) = 1) {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ i, |(μ (E i)).toReal - (ν (F i)).toReal| ≤ ε)
    (B : Set (X × Y)) (hB : ∀ i, Disjoint B (E i ×ˢ F i)) :
    finitePartitionCoupling μ ν E F B ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
  have hsum : ∑ i, ν (F i) = 1 := by
    simpa only [measure_iUnion hdF hF, tsum_fintype] using hcover
  exact ((finitePartitionCoupling_spec μ ν hE hF hdE hdF).2.2.2 B hB).trans
    (commonCellDeficit_le (fun i => μ (E i)) (fun i => ν (F i))
      (fun i => measure_ne_top μ (E i)) (fun i => measure_ne_top ν (F i)) hsum hε herror)

end BouRabeeGwynne
