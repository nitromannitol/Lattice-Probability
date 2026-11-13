/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ContinuousTimeMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.FiniteTimeMaximal
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Bases

/-!
Strict-threshold continuous-time maximal bounds. The proof reuses Doob's
finite sampled-time inequality, existing sorted finite sets, continuity of
measure from below, and a countable dense time set. Only almost-sure right
continuity is needed; cadlag paths are a direct corollary. No bounded-path or
continuous-path assumption, completion, or joint measurability is added.
-/
set_option autoImplicit false
open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Any finite collection of times before `T` is controlled by the terminal
mean. Sorting is mathlib's existing order embedding, with `T` appended. -/
theorem finite_set_time_maximal {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (hX : Submartingale X F P) (h0 : ∀ t ω, 0 ≤ X t ω)
    (T : ℝ≥0) (S : Finset ℝ≥0) (hS : ∀ s ∈ S, s ≤ T) (ε : ℝ≥0) :
    ε * P {ω | ∃ s ∈ S, (ε : ℝ) < X s ω} ≤
      ENNReal.ofReal (∫ ω, X T ω ∂P) := by
  classical
  let t : ℕ → ℝ≥0 := fun k =>
    if hk : k < S.card then S.orderEmbOfFin rfl ⟨k, hk⟩ else T
  have ht : Monotone t := by
    intro i j hij
    by_cases hi : i < S.card
    · by_cases hj : j < S.card
      · simpa only [t, dite_eq_left hi, dite_eq_left hj] using
          (S.orderEmbOfFin rfl).monotone (show (⟨i, hi⟩ : Fin S.card) ≤ ⟨j, hj⟩ from hij)
      · simpa only [t, dite_eq_left hi, dite_eq_right hj] using
          hS _ (S.orderEmbOfFin_mem rfl ⟨i, hi⟩)
    · have hj : ¬ j < S.card := fun hj => hi (hij.trans_lt hj)
      simp only [t, dite_eq_right hi, dite_eq_right hj, le_refl]
  have hlast : t S.card = T := by simp [t]
  have hsub : {ω | ∃ s ∈ S, (ε : ℝ) < X s ω} ⊆
      {ω | (ε : ℝ) ≤ (range (S.card + 1)).sup' nonempty_range_add_one
        (fun k => X (t k) ω)} := by
    rintro ω ⟨s, hs, hε⟩
    have hrs : s ∈ Set.range (S.orderEmbOfFin rfl) := by
      simpa only [S.range_orderEmbOfFin rfl, Finset.mem_coe] using hs
    obtain ⟨i, hi⟩ := hrs
    have hit : t i.val = s := by simp only [t, dite_eq_left i.isLt, hi]
    have himem : i.val ∈ range (S.card + 1) :=
      mem_range.mpr (i.isLt.trans (Nat.lt_succ_self _))
    exact hε.le.trans (hit ▸ Finset.le_sup' (fun k => X (t k) ω) himem)
  exact (mul_le_mul_right (measure_mono hsub) (ε : ℝ≥0∞)).trans
    (by simpa only [hlast] using finite_time_maximal hX h0 t ht ε S.card)

/-- The maximal bound for any countable set of observation times before `T`.
The directed finite unions need no extra measurability assumptions. -/
theorem countable_set_time_maximal {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (hX : Submartingale X F P) (h0 : ∀ t ω, 0 ≤ X t ω)
    (T : ℝ≥0) (D : Set ℝ≥0) (hD : D.Countable)
    (hDT : ∀ t ∈ D, t ≤ T) (ε : ℝ≥0) :
    ε * P {ω | ∃ t ∈ D, (ε : ℝ) < X t ω} ≤
      ENNReal.ofReal (∫ ω, X T ω ∂P) := by
  classical
  have : Countable D := hD.to_subtype
  let E : Finset D → Set Ω := fun S => {ω | ∃ t ∈ S, (ε : ℝ) < X t.val ω}
  have hmono : Monotone E := by
    intro S U hSU ω hω
    obtain ⟨t, ht, hε⟩ := hω
    exact ⟨t, hSU ht, hε⟩
  have hu : (⋃ S : Finset D, E S) = {ω | ∃ t ∈ D, (ε : ℝ) < X t ω} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hω
      obtain ⟨t, ht, hε⟩ := hS
      exact ⟨t.val, t.property, hε⟩
    · rintro ⟨t, ht, hε⟩
      apply Set.mem_iUnion.mpr
      exact ⟨{⟨t, ht⟩}, ⟨⟨t, ht⟩, mem_singleton_self _, hε⟩⟩
  have hbound : ∀ S : Finset D, (ε : ℝ≥0∞) * P (E S) ≤
      ENNReal.ofReal (∫ ω, X T ω ∂P) := by
    intro S
    have hsT : ∀ t ∈ S.image Subtype.val, t ≤ T := by
      rintro t ht
      obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
      exact hDT u.val u.property
    have he : E S = {ω | ∃ t ∈ S.image Subtype.val, (ε : ℝ) < X t ω} := by
      ext ω
      simp [E]
    rw [he]
    exact finite_set_time_maximal hX h0 T _ hsT ε
  rw [← hu, hmono.directed_le.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hbound

/-- Strict exceedance of a right-continuous path is detected by a dense time
set before `T`, together with `T` itself. No left continuity is needed. -/
theorem rightContinuous_exceedance_dense {f : ℝ≥0 → ℝ}
    (hf : IsRightContinuous f) {D : Set ℝ≥0} (hD : Dense D)
    (T : ℝ≥0) (ε : ℝ) :
    (∃ t ∈ Icc 0 T, ε < f t) ↔
      ∃ t ∈ insert T (D ∩ Iic T), ε < f t := by
  constructor
  · rintro ⟨t, ht, hε⟩
    rcases ht.2.eq_or_lt with h | h
    · subst t
      exact ⟨T, Or.inl rfl, hε⟩
    · have hgt : ∀ᶠ s in 𝓝[>] t, ε < f s := (hf t).eventually (eventually_gt_nhds hε)
      have hbefore : ∀ᶠ s in 𝓝[>] t, s < T :=
        nhdsWithin_le_nhds (eventually_lt_nhds h)
      obtain ⟨u, htu, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hgt.and hbefore)
      obtain ⟨s, hsD, hs⟩ := hD.exists_between htu
      exact ⟨s, Set.mem_insert_of_mem _ ⟨hsD, (hu hs).2.le⟩, (hu hs).1⟩
  · rintro ⟨t, ht, hε⟩
    rcases ht with rfl | ht
    · exact ⟨_, ⟨zero_le, le_rfl⟩, hε⟩
    · exact ⟨t, ⟨zero_le, ht.2⟩, hε⟩

/-- Continuous-time Doob bound with strict threshold, on a bounded horizon.
Only almost-sure right continuity is imposed. The potentially uncountable
supremum event is a.e. equal to a countable observation event, so the ambient
probability space need not be completed. -/
theorem continuous_time_maximal_of_ae_rightContinuous
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (hX : Submartingale X F P) (h0 : ∀ t ω, 0 ≤ X t ω)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => X t ω)) (T ε : ℝ≥0) :
    ε * P {ω | ∃ t ∈ Icc 0 T, (ε : ℝ) < X t ω} ≤
      ENNReal.ofReal (∫ ω, X T ω ∂P) := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hcount : (insert T (D ∩ Iic T)).Countable := (hDcount.mono inter_subset_left).insert T
  have hDT : ∀ t ∈ insert T (D ∩ Iic T), t ≤ T := by
    intro t ht
    rcases ht with rfl | ht
    · exact le_rfl
    · exact ht.2
  have he : {ω | ∃ t ∈ Icc 0 T, (ε : ℝ) < X t ω} =ᵐ[P]
      {ω | ∃ t ∈ insert T (D ∩ Iic T), (ε : ℝ) < X t ω} := by
    filter_upwards [hr] with ω hω
    exact propext (rightContinuous_exceedance_dense hω hDdense T ε)
  rw [measure_congr he]
  exact countable_set_time_maximal hX h0 T _ hcount hDT ε

/-- The cadlag-path form consumed by reflected-martingale localization. -/
theorem continuous_time_maximal_of_ae_cadlag
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (hX : Submartingale X F P) (h0 : ∀ t ω, 0 ≤ X t ω)
    (hc : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) (T ε : ℝ≥0) :
    ε * P {ω | ∃ t ∈ Icc 0 T, (ε : ℝ) < X t ω} ≤
      ENNReal.ofReal (∫ ω, X T ω ∂P) :=
  continuous_time_maximal_of_ae_rightContinuous hX h0
    (hc.mono fun _ h => h.isRightContinuous) T ε

end ReflectedGMS.MartingaleLimit
