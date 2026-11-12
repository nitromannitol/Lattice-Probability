/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.G4CMeasLusin at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Lusin's theorem: analytic sets are universally measurable (task G4C-LUSIN)

For a finite (or s-finite) Borel measure `μ` on a Polish space, every analytic set is
`μ`-null-measurable; hence so is every coanalytic set.

Source: A. S. Kechris, *Classical Descriptive Set Theory*, Springer GTM 156, Theorem 21.10
(p. 155), via the capacitability argument of Theorem 30.13 / 29.7; equivalently D. L. Cohn,
*Measure Theory*, 2nd ed., Proposition 8.4.1 ff. We follow the classical proof: write
`s = range f` with `f : (ℕ → ℕ) → X` continuous, choose bounds `m` recursively so that
`μ (f '' {x | ∀ i < k, x i ≤ m i})` stays within `ε` of `μ s` (outer measure is continuous
along increasing unions of arbitrary sets), and show that the decreasing intersection of the
closures of these images lies in the compact set `f '' {x | ∀ i, x i ≤ m i}` (here by a
sequential compactness argument instead of the finite-cover argument of the source).
-/

namespace QuantumZipper.Thm18Asm.G4Core

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- The cylinder of sequences bounded by `m` in the first `k` coordinates. -/
def lusinCyl (k : ℕ) (m : ℕ → ℕ) : Set (ℕ → ℕ) := {x | ∀ i < k, x i ≤ m i}

/-- The compact box of sequences bounded by `m` everywhere. -/
def lusinBox (m : ℕ → ℕ) : Set (ℕ → ℕ) := {x | ∀ i, x i ≤ m i}

lemma lusinBox_isCompact (m : ℕ → ℕ) : IsCompact (lusinBox m) := by
  have : lusinBox m = Set.pi univ (fun i => Iic (m i)) := by
    ext x; simp [lusinBox, Pi.le_def]
  rw [this]
  exact isCompact_univ_pi (fun i => (Set.finite_Iic (m i)).isCompact)

lemma lusinCyl_congr {k : ℕ} {m m' : ℕ → ℕ} (h : ∀ i < k, m i = m' i) :
    lusinCyl k m = lusinCyl k m' := by
  ext x
  simp only [lusinCyl, mem_ofPred_eq]
  exact ⟨fun hx i hi => h i hi ▸ hx i hi, fun hx i hi => (h i hi).symm ▸ hx i hi⟩

lemma lusinCyl_zero (m : ℕ → ℕ) : lusinCyl 0 m = univ := by
  ext x; simp [lusinCyl]

lemma lusinCyl_antitone (m : ℕ → ℕ) : Antitone (fun k => lusinCyl k m) := by
  intro k l hkl x hx i hi
  exact hx i (lt_of_lt_of_le hi hkl)

lemma lusinCyl_eq_iUnion (k : ℕ) (m : ℕ → ℕ) :
    lusinCyl k m = ⋃ j, lusinCyl (k + 1) (Function.update m k j) := by
  ext x
  simp only [lusinCyl, mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hx
    refine ⟨x k, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [Function.update_of_ne hi.ne]; exact hx i hi
    · simp
  · rintro ⟨j, hj⟩ i hi
    have := hj i (Nat.lt_succ_of_lt hi)
    rwa [Function.update_of_ne hi.ne] at this

lemma lusinCyl_mono_update (k : ℕ) (m : ℕ → ℕ) :
    Monotone (fun j => lusinCyl (k + 1) (Function.update m k j)) := by
  intro j j' hjj' x hx i hi
  have := hx i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · rwa [Function.update_of_ne hi.ne] at this ⊢
  · simp only [Function.update_self] at this ⊢
    exact this.trans hjj'

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

omit [TopologicalSpace X] in
/-- One step of the recursion: the next bound can be chosen losing at most `ε`. -/
lemma lusin_step (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) (k : ℕ) (m : ℕ → ℕ) :
    ∃ j, μ (f '' lusinCyl k m) ≤ μ (f '' lusinCyl (k + 1) (Function.update m k j)) + ε := by
  have hsup : μ (f '' lusinCyl k m) =
      ⨆ j, μ (f '' lusinCyl (k + 1) (Function.update m k j)) := by
    rw [lusinCyl_eq_iUnion k m, image_iUnion]
    exact Monotone.measure_iUnion (fun j j' h => image_mono (lusinCyl_mono_update k m h))
  have hlt : μ (f '' lusinCyl k m) < μ (f '' lusinCyl k m) + ε :=
    ENNReal.lt_add_right (measure_ne_top _ _) hε
  rw [hsup, ENNReal.iSup_add] at hlt
  obtain ⟨j, hj⟩ := lt_iSup_iff.1 hlt
  refine ⟨j, ?_⟩
  rw [hsup]
  exact hj.le

/-- The recursively chosen bounds: `lusinSeq` at stage `k`. -/
noncomputable def lusinSeq (J : ℕ → (ℕ → ℕ) → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun _ => 0
  | k + 1 => Function.update (lusinSeq J k) k (J k (lusinSeq J k))

/-- The limiting bound sequence. -/
noncomputable def lusinLim (J : ℕ → (ℕ → ℕ) → ℕ) : ℕ → ℕ := fun i => lusinSeq J (i + 1) i

lemma lusinSeq_agree (J : ℕ → (ℕ → ℕ) → ℕ) :
    ∀ k, ∀ i < k, lusinSeq J k i = lusinLim J i := by
  intro k
  induction k with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · simp only [lusinSeq]
      rw [Function.update_of_ne hi.ne]
      exact ih i hi
    · rfl

omit [MeasurableSpace X] in
/-- Key compactness step: the intersection of the closures of the images of the cylinders
lies in the image of the box. -/
lemma lusin_iInter_closure_subset [T2Space X] [FirstCountableTopology X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) (m : ℕ → ℕ) :
    (⋂ k, closure (f '' lusinCyl k m)) ⊆ f '' lusinBox m := by
  intro y hy
  rw [mem_iInter] at hy
  obtain ⟨U, hU⟩ := (𝓝 y).exists_antitone_basis
  have hex : ∀ k, ∃ x, x ∈ lusinCyl k m ∧ f x ∈ U k := by
    intro k
    obtain ⟨z, hzU, x, hx, rfl⟩ := mem_closure_iff_nhds.1 (hy k) (U k) (hU.mem k)
    exact ⟨x, hx, hzU⟩
  choose x hxC hxU using hex
  set g : ℕ → (ℕ → ℕ) := fun k i => min (x k i) (m i) with hg
  have hgK : ∀ k, g k ∈ lusinBox m := fun k i => min_le_right _ _
  obtain ⟨a, haK, φ, hφ, hconv⟩ := (lusinBox_isCompact m).tendsto_subseq hgK
  have hxconv : Tendsto (x ∘ φ) atTop (𝓝 a) := by
    rw [tendsto_pi_nhds] at hconv ⊢
    intro i
    refine (hconv i).congr' ?_
    refine Filter.eventually_atTop.2 ⟨i + 1, fun k hk => ?_⟩
    have hik : i < φ k := lt_of_lt_of_le (Nat.lt_of_succ_le hk) (hφ.id_le k)
    simp [g, min_eq_left (hxC (φ k) i hik)]
  have h1 : Tendsto (fun k => f (x (φ k))) atTop (𝓝 (f a)) :=
    (hf.tendsto a).comp hxconv
  have h2 : Tendsto (fun k => f (x (φ k))) atTop (𝓝 y) :=
    (hU.tendsto hxU).comp hφ.tendsto_atTop
  exact ⟨a, haK, tendsto_nhds_unique h1 h2⟩

/-- Inner approximation of the range of a continuous map on Baire space by compact sets
(Kechris, Thm 21.10 / 30.13). -/
lemma lusin_inner [T2Space X] [FirstCountableTopology X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : (ℕ → ℕ) → X} (hf : Continuous f)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ K, IsCompact K ∧ K ⊆ range f ∧ μ (range f) ≤ μ K + δ := by
  obtain ⟨ε', hε'pos, hsum⟩ := ENNReal.exists_pos_sum_of_countable hδ ℕ
  have hstep := fun k m => lusin_step μ f (ε := (ε' k : ℝ≥0∞))
    (by simpa using (hε'pos k).ne') k m
  choose J hJ using hstep
  set m := lusinLim J with hm
  have hbound : ∀ k, μ (range f) ≤
      μ (f '' lusinCyl k m) + ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := by
    intro k
    induction k with
    | zero => simp [lusinCyl_zero, image_univ]
    | succ k ih =>
      have e1 : lusinCyl k m = lusinCyl k (lusinSeq J k) :=
        lusinCyl_congr (fun i hi => (lusinSeq_agree J k i hi).symm)
      have e2 : lusinCyl (k + 1) m = lusinCyl (k + 1) (lusinSeq J (k + 1)) :=
        lusinCyl_congr (fun i hi => (lusinSeq_agree J (k + 1) i hi).symm)
      calc μ (range f) ≤ μ (f '' lusinCyl k m) + ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := ih
        _ ≤ (μ (f '' lusinCyl (k + 1) m) + ε' k) + ∑ i ∈ Finset.range k, (ε' i : ℝ≥0∞) := by
          gcongr
          rw [e1, e2]
          exact hJ k (lusinSeq J k)
        _ = _ := by rw [Finset.sum_range_succ]; ring
  have hbound' : ∀ k, μ (range f) ≤ μ (closure (f '' lusinCyl k m)) + δ := fun k =>
    (hbound k).trans (add_le_add (measure_mono subset_closure)
      ((ENNReal.sum_le_tsum _).trans hsum.le))
  have hanti : Antitone (fun k => closure (f '' lusinCyl k m)) := fun k l h =>
    closure_mono (image_mono (lusinCyl_antitone m h))
  have hinter : μ (⋂ k, closure (f '' lusinCyl k m)) = ⨅ k, μ (closure (f '' lusinCyl k m)) :=
    hanti.measure_iInter (fun k => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  refine ⟨f '' lusinBox m, (lusinBox_isCompact m).image hf, image_subset_range _ _, ?_⟩
  calc μ (range f) ≤ (⨅ k, μ (closure (f '' lusinCyl k m))) + δ := by
        rw [ENNReal.iInf_add]; exact le_iInf hbound'
    _ = μ (⋂ k, closure (f '' lusinCyl k m)) + δ := by rw [hinter]
    _ ≤ μ (f '' lusinBox m) + δ := by
        gcongr; exact lusin_iInter_closure_subset hf m

/-- A set that is inner-approximable in measure by compact sets is null-measurable. -/
lemma nullMeasurableSet_of_compact_inner [T2Space X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X}
    (h : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ K, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + δ) :
    NullMeasurableSet s μ := by
  have h' : ∀ n : ℕ, ∃ K, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + (n : ℝ≥0∞)⁻¹ := fun n =>
    h _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose K hKc hKs hKμ using h'
  have hT : MeasurableSet (⋃ n, K n) := MeasurableSet.iUnion fun n => (hKc n).measurableSet
  have hTs : (⋃ n, K n) ⊆ s := iUnion_subset hKs
  have hle : μ s ≤ μ (⋃ n, K n) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
    exact (hKμ n).trans (add_le_add (measure_mono (subset_iUnion K n)) hn.le)
  have h0 : μ (s \ ⋃ n, K n) = 0 := by
    have h1 := measure_inter_add_sdiff (μ := μ) s hT
    rw [inter_eq_right.2 hTs] at h1
    have : μ (⋃ n, K n) + μ (s \ ⋃ n, K n) ≤ μ (⋃ n, K n) + 0 := by
      rw [add_zero, h1]; exact hle
    exact le_antisymm ((ENNReal.add_le_add_iff_left (measure_ne_top μ _)).1 this) zero_le
  rw [← union_sdiff_cancel hTs]
  exact hT.nullMeasurableSet.union (NullMeasurableSet.of_null h0)

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- **Lusin's theorem** (Kechris, *Classical Descriptive Set Theory*, Thm 21.10): an analytic
subset of a Polish space is null-measurable for every finite Borel measure. -/
theorem analyticSet_nullMeasurableSet [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} (hs : AnalyticSet s) (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  · exact nullMeasurableSet_of_compact_inner μ (fun δ hδ => lusin_inner μ hf hδ)

end QuantumZipper.Thm18Asm.G4Core
