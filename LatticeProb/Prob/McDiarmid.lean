/-
McDiarmid's bounded-differences inequality for a finite product of probability spaces.

For `f` on `∀ i, Ω i` whose one-coordinate oscillation is bounded, `|f x - f y| ≤ c i` whenever
`x` and `y` agree off `i`, and for `t ≥ 0`, `mcdiarmid` bounds the upper tail of `f` about its
mean by `exp(-2 t² / ∑ i, c i²)`.

The route tensorizes by marginals instead of building a martingale. `rmarg μ s f x` integrates
`f` over the coordinates in `s`, the real-valued analogue of Mathlib's `MeasureTheory.lmarginal`
(notation `∫⋯∫⁻_s, F ∂μ`). Induction over `s` shows
`(∫⋯∫⁻_s, e^{λ f} ∂μ) x ≤ exp(λ · rmarg μ s f x + λ² ∑_{i∈s} c_i² / 8)`, peeling one coordinate
`i` at a time with `lmarginal_insert` and applying Hoeffding's lemma to
`z ↦ rmarg μ s f (update x i z)`, which has oscillation at most `c i` and mean
`rmarg μ (insert i s) f x`. At `s = univ` this is the subgaussian MGF bound, and
`HasSubgaussianMGF.measure_ge_le` finishes.

The proof was written by the library's proof fleet (deepseek-v4.1-flash and Mistral leanstral)
from a statement-owned decomposition and verified by the library gates.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace LatticeProb

namespace McDiarmidAux

/-- Integrate `f` over the coordinates in `s` (real-valued marginal). -/
private noncomputable def rmarg {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) (s : Finset ι)
    (f : (∀ i, Ω i) → ℝ) (x : ∀ i, Ω i) : ℝ :=
  ∫ y : (∀ i : s, Ω i), f (Function.updateFinset x s y) ∂Measure.pi (fun i : s => μ i)

-- Finset.induction_on s generalizing x y; step: z := Function.update x i (y i);
-- z,y agree off s; x,z agree off i (Function.update_self/update_of_ne); abs_sub_le, Finset.sum_insert.
private theorem aux_mcd_ind {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    ∀ (t : Finset ι) (x y : (∀ i, Ω i)), (∀ j, j ∉ t → x j = y j) →
      |f x - f y| ≤ ∑ i ∈ t, c i := by
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro x y h
      have hxy : x = y := funext fun j => h j (by simp)
      subst hxy
      simp
  | insert a t hat ih =>
      intro x y h
      have hxz : |f x - f (Function.update x a (y a))| ≤ c a := by
        apply hbd a x
        intro j hj
        rw [Function.update_of_ne hj]
      have hzy : |f (Function.update x a (y a)) - f y| ≤ ∑ i ∈ t, c i := by
        exact ih (Function.update x a (y a)) y (fun j hj => by
          by_cases hja : j = a
          · rw [hja, Function.update_self]
          · rw [Function.update_of_ne hja]
            exact h j (by simp only [Finset.mem_insert, not_or]; exact ⟨hja, hj⟩))
      calc |f x - f y|
          ≤ |f x - f (Function.update x a (y a))| + |f (Function.update x a (y a)) - f y| :=
            abs_sub_le _ _ _
        _ ≤ c a + ∑ i ∈ t, c i := add_le_add hxz hzy
        _ = ∑ i ∈ insert a t, c i := by rw [Finset.sum_insert hat]

private theorem aux_mcdiarmid_1 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (s : Finset ι) : ∀ x y : (∀ i, Ω i), (∀ j, j ∉ s → x j = y j) →
      |f x - f y| ≤ ∑ i ∈ s, c i := by
  intro x y h
  exact aux_mcd_ind f c hbd s x y h


-- hbd i x x (fun _ _ => rfl) gives |f x - f x| ≤ c i; simp.
private theorem aux_mcdiarmid_2 {ι : Type*} {Ω : ι → Type*} [∀ i, Nonempty (Ω i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (i : ι) : 0 ≤ c i := by
  have h := hbd i (Classical.arbitrary (∀ i, Ω i)) (Classical.arbitrary (∀ i, Ω i))
    (fun _ _ => rfl)
  simpa using h


-- Fix x₀ := Classical.arbitrary; B := |f x₀| + ∑ i, c i; aux_mcdiarmid_1 with s = Finset.univ
-- (Finset.mem_univ), then abs_sub_abs_le_abs_sub.
private theorem aux_mcdiarmid_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Nonempty (Ω i)] (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    ∃ B : ℝ, ∀ x, |f x| ≤ B := by
  classical
  refine ⟨|f (fun i => Classical.arbitrary (Ω i))| + ∑ i, c i, fun x => ?_⟩
  have h := aux_mcdiarmid_1 f c hbd Finset.univ x (fun i => Classical.arbitrary (Ω i)) (fun j hj => by simp at hj)
  have h2 := abs_sub_abs_le_abs_sub (f x) (f (fun i => Classical.arbitrary (Ω i)))
  linarith


-- Copy of `MeasureTheory.lmarginal_empty`: simp_rw [rmarg, Measure.pi_of_empty], then
-- integral_dirac' (Subsingleton.stronglyMeasurable) and Function.updateFinset_empty.
private theorem aux_mcdiarmid_4 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i))
    (f : (∀ i, Ω i) → ℝ) (x : ∀ i, Ω i) : rmarg μ ∅ f x = f x := by
  unfold rmarg
  rw [Measure.pi_of_empty (fun i : (∅ : Finset ι) => μ i)]
  simp [Function.updateFinset_empty]


-- Copy of `MeasureTheory.lmarginal_univ` with `integral_map_equiv` in place of
-- `lintegral_map_equiv`: e := Equiv.subtypeUnivEquiv Finset.mem_univ,
-- (measurePreserving_piCongrLeft μ e).integral_map_equiv, Function.updateFinset_def, simp.
private theorem aux_mcdiarmid_5 {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : (∀ i, Ω i) → ℝ) (x : ∀ i, Ω i) :
    rmarg μ Finset.univ f x = ∫ y, f y ∂(Measure.pi μ) := by
  let e : { j // j ∈ Finset.univ } ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ
  have h := (measurePreserving_piCongrLeft μ e).integral_comp' f
  simp only [rmarg]
  rw [← h]
  congr 1
  funext y
  rw [Function.updateFinset_univ]
  congr 1


-- (hf.comp measurable_updateFinset').stronglyMeasurable.integral_prod_right' gives strong
-- measurability of x ↦ ∫ y, f (updateFinset x s y); then .measurable.
-- (Name: MeasureTheory.StronglyMeasurable.integral_prod_right'; needs SFinite.)
private theorem aux_mcdiarmid_6 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) :
    Measurable (rmarg μ s f) := by
  have hm : StronglyMeasurable
      (fun p : (∀ i, Ω i) × (∀ i : s, Ω i) => f (Function.updateFinset p.1 s p.2)) :=
    (hf.comp measurable_updateFinset').stronglyMeasurable
  exact (hm.integral_prod_right').measurable


-- rmarg only depends on coordinates outside s. Copy of `MeasureTheory.lmarginal_congr`:
-- dsimp only [rmarg, Function.updateFinset_def]; rcongr; exact h _ ‹_›.
private theorem aux_mcdiarmid_7 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) (s : Finset ι)
    (f : (∀ i, Ω i) → ℝ) {x y : ∀ i, Ω i} (h : ∀ i ∉ s, x i = y i) :
    rmarg μ s f x = rmarg μ s f y := by
  dsimp only [rmarg, Function.updateFinset_def]
  rcongr
  exact h _ ‹_›


-- Fubini: Bochner copy of `MeasureTheory.lmarginal_union`: rewrite with
-- (measurePreserving_piFinsetUnion hst μ).integral_map_equiv, then `integral_prod`
-- (integrability: Integrable.of_bound, bound B, measurability from measurable_updateFinset'
-- composed with (MeasurableEquiv.piFinsetUnion _ hst).measurable), then
-- Function.updateFinset_updateFinset hst.  -- SPLIT? (≈20 lines in Mathlib's lintegral version)
private theorem aux_mcdiarmid_8 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    {s t : Finset ι} (hst : Disjoint s t) (x : ∀ i, Ω i) :
    rmarg μ (s ∪ t) f x = rmarg μ s (rmarg μ t f) x := by
  let e := MeasurableEquiv.piFinsetUnion Ω hst
  have hmap : Measure.map (⇑e)
      ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))) =
      Measure.pi (fun i : ↥(s ∪ t) => μ i) :=
    (measurePreserving_piFinsetUnion hst μ).map_eq
  have hB' : ∀ p : ((i : s) → Ω i) × ((i : t) → Ω i),
      ‖f (Function.updateFinset x (s ∪ t) (e p))‖ ≤ B :=
    fun p => (by rw [Real.norm_eq_abs]; exact hB _)
  have hint : Integrable (fun p : ((i : s) → Ω i) × ((i : t) → Ω i) =>
        f (Function.updateFinset x (s ∪ t) (e p)))
      ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun i : t => μ i))) :=
    Integrable.of_bound (hf.comp (measurable_updateFinset.comp e.measurable)).aestronglyMeasurable
      B (ae_of_all _ hB')
  rw [show rmarg μ (s ∪ t) f x =
      (∫ y : (i : ↥(s ∪ t)) → Ω i, f (Function.updateFinset x (s ∪ t) y)
        ∂Measure.pi (fun i : ↥(s ∪ t) => μ i)) from rfl]
  rw [← hmap]
  rw [integral_map_equiv]
  rw [integral_prod _ hint]
  simp_rw [rmarg, Function.updateFinset_updateFinset hst]
  rfl


-- Copy of `MeasureTheory.lmarginal_singleton`: e := (MeasurableEquiv.piUnique _).symm,
-- (measurePreserving_piUnique _).symm _ |>.integral_map_equiv, Function.update_eq_updateFinset.
private theorem aux_mcdiarmid_9 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (i : ι) (x : ∀ i, Ω i) :
    rmarg μ {i} f x = ∫ z, f (Function.update x i z) ∂(μ i) := by
  rw [rmarg]
  let e := (MeasurableEquiv.piUnique fun j : ({i} : Finset ι) => Ω j).symm
  have hpe : MeasurePreserving (⇑e) (μ i) (Measure.pi fun j : ({i} : Finset ι) => μ j) :=
    (measurePreserving_piUnique fun j : ({i} : Finset ι) => μ j).symm
  rw [← hpe.integral_comp' (fun Y => f (Function.updateFinset x {i} Y))]
  simp [e, Function.update_eq_updateFinset]


-- Finset.insert_eq, aux_mcdiarmid_8 with Finset.disjoint_singleton_left.mpr hi, aux_mcdiarmid_9.
private theorem aux_mcdiarmid_10 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    {s : Finset ι} {i : ι} (hi : i ∉ s) (x : ∀ i, Ω i) :
    rmarg μ (insert i s) f x = ∫ z, rmarg μ s f (Function.update x i z) ∂(μ i) := by
  rw [Finset.insert_eq]
  rw [aux_mcdiarmid_8 μ f hf B hB (s := {i}) (t := s) (Finset.disjoint_singleton_left.mpr hi) x]
  exact aux_mcdiarmid_9 μ (rmarg μ s f) i x


-- rmarg difference = ∫ y, (f p - f q) with p q := updateFinset (update x i z/z') s y (integral_sub,
-- integrability via Integrable.of_bound); p,q differ only at i (i ∉ s; Function.updateFinset_def,
-- Function.update_of_ne), so hbd gives ‖f p - f q‖ ≤ c i; conclude with
-- norm_integral_le_of_norm_le_const and measureReal_univ_eq_one (prob. measure).
private theorem aux_mcdiarmid_11 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    {s : Finset ι} {i : ι} (_hi : i ∉ s) (x : ∀ i, Ω i) (z z' : Ω i) :
    rmarg μ s f (Function.update x i z) - rmarg μ s f (Function.update x i z') ≤ c i := by
  haveI hp : IsProbabilityMeasure (Measure.pi (fun j : s => μ j)) := inferInstance
  have hoff : ∀ j, j ≠ i → Function.update x i z j = Function.update x i z' j := by
    intro j hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]
  have hpoint : ∀ y : (∀ j : s, Ω j),
      |f (Function.updateFinset (Function.update x i z) s y) -
        f (Function.updateFinset (Function.update x i z') s y)| ≤ c i := by
    intro y
    refine hbd i _ _ ?_
    intro j hj
    by_cases hjs : j ∈ s
    · simp only [Function.updateFinset_def, dif_pos hjs]
    · simp only [Function.updateFinset_def, dif_neg hjs]
      exact hoff j hj
  have hI1 : Integrable (fun y : (∀ j : s, Ω j) =>
      f (Function.updateFinset (Function.update x i z) s y)) (Measure.pi (fun j : s => μ j)) :=
    Integrable.of_bound (hf.comp measurable_updateFinset).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hB (Function.updateFinset (Function.update x i z) s y))
  have hI2 : Integrable (fun y : (∀ j : s, Ω j) =>
      f (Function.updateFinset (Function.update x i z') s y)) (Measure.pi (fun j : s => μ j)) :=
    Integrable.of_bound (hf.comp measurable_updateFinset).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hB (Function.updateFinset (Function.update x i z') s y))
  have hkey : rmarg μ s f (Function.update x i z) - rmarg μ s f (Function.update x i z')
      = ∫ y : (∀ j : s, Ω j), (f (Function.updateFinset (Function.update x i z) s y) -
          f (Function.updateFinset (Function.update x i z') s y))
          ∂(Measure.pi (fun j : s => μ j)) := by
    simp only [rmarg]
    rw [integral_sub hI1 hI2]
  rw [hkey]
  calc ∫ y : (∀ j : s, Ω j), (f (Function.updateFinset (Function.update x i z) s y) -
          f (Function.updateFinset (Function.update x i z') s y))
          ∂(Measure.pi (fun j : s => μ j))
      ≤ ‖∫ y : (∀ j : s, Ω j), (f (Function.updateFinset (Function.update x i z) s y) -
          f (Function.updateFinset (Function.update x i z') s y))
          ∂(Measure.pi (fun j : s => μ j))‖ := Real.le_norm_self _
    _ ≤ c i * (Measure.pi (fun j : s => μ j)).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hpoint y)
    _ = c i := by rw [probReal_univ, mul_one]


-- a := ⨅ z, g z (bounded below by g z₀ - c). g z ≥ a: ciInf_le ⟨g z₀ - c, _⟩.
-- g z ≤ a + c: le_ciInf (fun z' => by linarith [h z z']) gives g z - c ≤ a.
private theorem aux_mcdiarmid_12 {α : Type*} [Nonempty α] (g : α → ℝ) (c : ℝ)
    (h : ∀ z z', g z - g z' ≤ c) : ∃ a, ∀ z, g z ∈ Set.Icc a (a + c) := by
  obtain ⟨z₀⟩ := ‹Nonempty α›
  have hbdd : BddBelow (Set.range g) :=
    ⟨g z₀ - c, by rintro _ ⟨z, rfl⟩; linarith [h z₀ z]⟩
  refine ⟨⨅ z, g z, fun z => ⟨?_, ?_⟩⟩
  · exact ciInf_le hbdd z
  · have h1 : g z - c ≤ ⨅ z', g z' := le_ciInf (f := g) fun z' => by linarith [h z z']
    linarith


-- Hoeffding's lemma: ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (hm := hg.aemeasurable)
-- (hb := ae_of_all _ hab) gives HasSubgaussianMGF (g - ν[g]) ((‖(a+c) - a‖₊/2)^2) ν;
-- its .mgf_le t; unfold ProbabilityTheory.mgf, rewrite exp(t(g-m)) = exp(-t m) * exp(t g)
-- (Real.exp_add / Real.exp_sub, integral_const_mul), simplify ‖c‖₊ with hc : 0 ≤ c
-- (Real.nnnorm_of_nonneg / NNReal.coe_pow), finish with Real.exp_add and nlinarith/ring_nf.
-- Variance proxy of Hoeffding's lemma on an interval of length c: (a+c)-a = c (ring),
-- ‖c‖₊ coerces to |c| = c (coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc); NNReal.coe_pow,
-- NNReal.coe_div; ring.
private theorem aux_mcdiarmid_13_1 (a c : ℝ) (hc : 0 ≤ c) :
    ((((‖((a + c) - a : ℝ)‖₊ / 2) ^ 2 : NNReal)) : ℝ) = c ^ 2 / 4 := by
  have h : ((‖((a + c) - a : ℝ)‖₊ : NNReal) : ℝ) = c := by
    rw [coe_nnnorm, show (a + c) - a = c by ring, Real.norm_eq_abs, abs_of_nonneg hc]
  push_cast [h]
  ring

-- Hoeffding's lemma, centred MGF form: ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
-- hg.aemeasurable (ae_of_all _ hab) (with b := a + c), its `.mgf_le t`, rewrite the proxy with
-- aux_mcdiarmid_13_1, and c²/4 · t²/2 = t² c²/8 (ring, via le_of_le_of_eq / convert … using 2).
private theorem aux_mcdiarmid_13_2 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : α → ℝ) (hg : Measurable g) (a c : ℝ) (hc : 0 ≤ c)
    (hab : ∀ z, g z ∈ Set.Icc a (a + c)) (t : ℝ) :
    mgf (fun z => g z - ∫ z, g z ∂ν) ν t ≤ Real.exp (t ^ 2 * c ^ 2 / 8) := by
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := ν) hg.aemeasurable (ae_of_all _ hab)).mgf_le t
  rw [aux_mcdiarmid_13_1 a c hc] at h
  exact h.trans (le_of_eq (by ring_nf))

-- Factor out the mean: unfold ProbabilityTheory.mgf; ← integral_const_mul; integral_congr_ae /
-- congr with funext; ← Real.exp_add; ring_nf.
private theorem aux_mcdiarmid_13_3 {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : α → ℝ) (t : ℝ) :
    ∫ z, Real.exp (t * g z) ∂ν
      = Real.exp (t * ∫ z, g z ∂ν) * mgf (fun z => g z - ∫ z, g z ∂ν) ν t := by
  unfold mgf
  rw [← integral_const_mul]
  congr 1
  funext z
  rw [← Real.exp_add]
  ring_nf

private theorem aux_mcdiarmid_13 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : α → ℝ) (hg : Measurable g) (a c : ℝ) (hc : 0 ≤ c)
    (hab : ∀ z, g z ∈ Set.Icc a (a + c)) (t : ℝ) :
    ∫ z, Real.exp (t * g z) ∂ν ≤ Real.exp (t * ∫ z, g z ∂ν + t ^ 2 * c ^ 2 / 8) := by
  rw [aux_mcdiarmid_13_3, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (aux_mcdiarmid_13_2 ν g hg a c hc hab t) (Real.exp_nonneg _)

-- ← ofReal_integral_eq_lintegral_ofReal (integrable: Integrable.of_bound with bound
-- exp(|t|·(|a|+|c|)); nonneg: Real.exp_pos) then ENNReal.ofReal_le_ofReal (aux_mcdiarmid_13).
private theorem aux_mcdiarmid_14 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : α → ℝ) (hg : Measurable g) (a c : ℝ) (hc : 0 ≤ c)
    (hab : ∀ z, g z ∈ Set.Icc a (a + c)) (t : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z)) ∂ν
      ≤ ENNReal.ofReal (Real.exp (t * ∫ z, g z ∂ν + t ^ 2 * c ^ 2 / 8)) := by
  have hbound : ∀ z, |g z| ≤ |a| + |c| := fun z => by
    rw [abs_le]
    constructor
    · have h1 : a ≤ g z := (hab z).1
      linarith [neg_abs_le a, abs_nonneg c]
    · have h2 : g z ≤ a + c := (hab z).2
      linarith [le_abs_self a, le_abs_self c]
  have hf_int : Integrable (fun z => Real.exp (t * g z)) ν :=
    Integrable.of_bound (hg.const_mul t).exp.aestronglyMeasurable
      (Real.exp (|t| * (|a| + |c|)))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 : t * g z ≤ |t * g z| := le_abs_self _
        rw [abs_mul] at h1
        have h2 : |t| * |g z| ≤ |t| * (|a| + |c|) :=
          mul_le_mul_of_nonneg_left (hbound z) (abs_nonneg t)
        linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int (ae_of_all _ fun z => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (aux_mcdiarmid_13 ν g hg a c hc hab t)


-- Pure ENNReal algebra: exp(t g + K) = exp K * exp(t g) (Real.exp_add, ENNReal.ofReal_mul),
-- lintegral_const_mul' (ofReal ≠ ⊤: ENNReal.ofReal_ne_top), mul_le_mul_left', then
-- ← ENNReal.ofReal_mul (Real.exp_nonneg), ← Real.exp_add, ring_nf.
private theorem aux_mcdiarmid_15a {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : α → ℝ) (t K : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z + K)) ∂ν
      = ENNReal.ofReal (Real.exp K) * ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z)) ∂ν := by
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z + K)) ∂ν
      = ∫⁻ z, ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (Real.exp (t * g z)) ∂ν := by
        apply lintegral_congr
        intro z
        rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos K)), ← Real.exp_add]
        congr 1
        ring_nf
    _ = ENNReal.ofReal (Real.exp K) * ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z)) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem aux_mcdiarmid_15b (t m K L : ℝ) :
    ENNReal.ofReal (Real.exp K) * ENNReal.ofReal (Real.exp (t * m + L))
      = ENNReal.ofReal (Real.exp (t * m + (K + L))) := by
  rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos K)), ← Real.exp_add]
  congr 1
  ring_nf

private theorem aux_mcdiarmid_15 {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (g : α → ℝ) (t m K L : ℝ) (A : ENNReal)
    (hA : A ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z + K)) ∂ν)
    (hg : ∫⁻ z, ENNReal.ofReal (Real.exp (t * g z)) ∂ν ≤ ENNReal.ofReal (Real.exp (t * m + L))) :
    A ≤ ENNReal.ofReal (Real.exp (t * m + (K + L))) := by
  exact le_trans (le_trans hA (le_of_eq (aux_mcdiarmid_15a ν g t K)))
    (le_trans (mul_le_mul_right hg _) (le_of_eq (aux_mcdiarmid_15b t m K L)))


-- Induction step. lmarginal_insert (measurable: (hf.const_mul t).exp.ennreal_ofReal) rewrites the
-- LHS as ∫⁻ z, (∫⋯∫⁻_s ..)(update x i z) ∂μ i ≤ (lintegral_mono, ih) ∫⁻ ofReal(exp(t g z + K));
-- g z := rmarg μ s f (update x i z), measurable by aux_mcdiarmid_6 comp measurable_update' ;
-- aux_mcdiarmid_12 + aux_mcdiarmid_11 give the Icc; aux_mcdiarmid_14; aux_mcdiarmid_10 identifies
-- ∫ g = rmarg μ (insert i s) f x; aux_mcdiarmid_15; Finset.sum_insert hi and ring for exponents.
-- SPLIT? (≈15-20 lines)
private theorem aux_mcdiarmid_16 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) {s : Finset ι} {i : ι} (hi : i ∉ s)
    (ih : ∀ x, (∫⋯∫⁻_s, (fun y => ENNReal.ofReal (Real.exp (t * f y))) ∂μ) x
      ≤ ENNReal.ofReal (Real.exp (t * rmarg μ s f x + t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8)))
    (x : ∀ i, Ω i) :
    (∫⋯∫⁻_(insert i s), (fun y => ENNReal.ofReal (Real.exp (t * f y))) ∂μ) x
      ≤ ENNReal.ofReal (Real.exp (t * rmarg μ (insert i s) f x
          + t ^ 2 * (∑ j ∈ insert i s, c j ^ 2) / 8)) := by
  letI : Nonempty (Ω i) := nonempty_of_isProbabilityMeasure (μ i)
  have hF : Measurable (fun y : (∀ i, Ω i) => ENNReal.ofReal (Real.exp (t * f y))) := ((hf.const_mul t).exp).ennreal_ofReal
  rw [lmarginal_insert _ hF hi]
  have hgm : Measurable (fun z : Ω i => rmarg μ s f (Function.update x i z)) := (aux_mcdiarmid_6 μ s f hf).comp (by fun_prop)
  have hbdd : ∀ z z' : Ω i, rmarg μ s f (Function.update x i z) - rmarg μ s f (Function.update x i z') ≤ c i := fun z z' => aux_mcdiarmid_11 μ f hf B hB c hbd hi x z z'
  obtain ⟨a, ha⟩ := aux_mcdiarmid_12 (fun z : Ω i => rmarg μ s f (Function.update x i z)) (c i) hbdd
  have hint : ∫ z, rmarg μ s f (Function.update x i z) ∂μ i = rmarg μ (insert i s) f x := (aux_mcdiarmid_10 μ f hf B hB hi x).symm
  have hg := aux_mcdiarmid_14 (μ i) (fun z : Ω i => rmarg μ s f (Function.update x i z)) hgm a (c i) (hc i) ha t
  rw [hint] at hg
  have hA : ∫⁻ z : Ω i, (∫⋯∫⁻_s, (fun y => ENNReal.ofReal (Real.exp (t * f y))) ∂μ) (Function.update x i z) ∂μ i ≤ ∫⁻ z : Ω i, ENNReal.ofReal (Real.exp (t * rmarg μ s f (Function.update x i z) + t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8)) ∂μ i := lintegral_mono fun z => ih (Function.update x i z)
  refine (aux_mcdiarmid_15 (μ i) (fun z : Ω i => rmarg μ s f (Function.update x i z)) t (rmarg μ (insert i s) f x) (t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8) (t ^ 2 * (c i) ^ 2 / 8) _ hA hg).trans (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [Finset.sum_insert hi]; ring_nf)))


-- Finset.induction_on s: empty case lmarginal_empty, aux_mcdiarmid_4, simp;
-- insert case aux_mcdiarmid_16.
private theorem aux_mcdiarmid_17 {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) (s : Finset ι) (x : ∀ i, Ω i) :
    (∫⋯∫⁻_s, (fun y => ENNReal.ofReal (Real.exp (t * f y))) ∂μ) x
      ≤ ENNReal.ofReal (Real.exp (t * rmarg μ s f x + t ^ 2 * (∑ j ∈ s, c j ^ 2) / 8)) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    simp [lmarginal_empty, aux_mcdiarmid_4]
  | insert i s hi ih =>
    exact aux_mcdiarmid_16 μ f hf B hB c hc hbd t hi ih x


-- aux_mcdiarmid_17 at s = univ, x := Classical.arbitrary; lintegral_eq_lmarginal_univ,
-- aux_mcdiarmid_5; convert via ofReal_integral_eq_lintegral_ofReal (integrable: Integrable.of_bound,
-- bound exp(|t| B)) and ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg); then
-- exp(t(f - m)) = exp(-t m) * exp(t f): integral_const_mul, Real.exp_add, Real.exp_le_exp-free
-- algebra: multiply the bound by exp(-t m) (mul_le_mul_of_nonneg_left).
private theorem aux_mcdiarmid_18_g {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * f z)) ∂(Measure.pi μ)
      ≤ ENNReal.ofReal (Real.exp (t * (∫ y, f y ∂(Measure.pi μ)) + t ^ 2 * (∑ j, c j ^ 2) / 8)) := by
  have hne : ∀ i, Nonempty (Ω i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  let x₀ : ∀ i, Ω i := fun i => Classical.choice (hne i)
  have h17 := aux_mcdiarmid_17 μ f hf B hB c hc hbd t Finset.univ x₀
  rw [lintegral_eq_lmarginal_univ (μ := μ) (f := fun y => ENNReal.ofReal (Real.exp (t * f y))) x₀]
  refine h17.trans (le_of_eq ?_)
  rw [aux_mcdiarmid_5 μ f x₀]

private theorem aux_mcdiarmid_18_main {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (F : α → ℝ) (hFm : Measurable F) (BF : ℝ) (hBF : ∀ z, |F z| ≤ BF) (t m K : ℝ)
    (hb : ∫⁻ z, ENNReal.ofReal (Real.exp (t * F z)) ∂ν
      ≤ ENNReal.ofReal (Real.exp (t * m + K))) :
    ∫ z, Real.exp (t * (F z - m)) ∂ν ≤ Real.exp K := by
  have hexpG : Integrable (fun z => Real.exp (t * F z)) ν :=
    Integrable.of_bound ((hFm.const_mul t).exp).aestronglyMeasurable (Real.exp (|t| * BF))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by
          calc t * F z ≤ |t * F z| := le_abs_self _
            _ = |t| * |F z| := abs_mul _ _
            _ ≤ |t| * BF := mul_le_mul_of_nonneg_left (hBF z) (abs_nonneg t)))
  have key2 : Integrable (fun z => Real.exp (-(t * m)) * Real.exp (t * F z)) ν :=
    hexpG.const_mul _
  have hInt : Integrable (fun z => Real.exp (t * (F z - m))) ν :=
    key2.congr (ae_of_all _ fun z => by
      simp only
      rw [← Real.exp_add]
      congr 1
      ring)
  have hnn : 0 ≤ᵐ[ν] fun z => Real.exp (t * (F z - m)) :=
    ae_of_all _ fun z => (Real.exp_pos _).le
  have key := ofReal_integral_eq_lintegral_ofReal hInt hnn
  have hcongr : ∫⁻ z, ENNReal.ofReal (Real.exp (t * (F z - m))) ∂ν
      = ENNReal.ofReal (Real.exp (-(t * m))) * ∫⁻ z, ENNReal.ofReal (Real.exp (t * F z)) ∂ν := by
    have hmeas : Measurable (fun z => ENNReal.ofReal (Real.exp (t * F z))) :=
      ((hFm.const_mul t).exp).ennreal_ofReal
    have hpoint : ∀ z : α, ENNReal.ofReal (Real.exp (t * (F z - m)))
        = ENNReal.ofReal (Real.exp (-(t * m))) * ENNReal.ofReal (Real.exp (t * F z)) := by
      intro z
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring
    rw [lintegral_congr hpoint, lintegral_const_mul _ hmeas]
  have hmain : ENNReal.ofReal (∫ z, Real.exp (t * (F z - m)) ∂ν) ≤ ENNReal.ofReal (Real.exp K) := by
    rw [key, hcongr]
    calc ENNReal.ofReal (Real.exp (-(t * m))) * ∫⁻ z, ENNReal.ofReal (Real.exp (t * F z)) ∂ν
        ≤ ENNReal.ofReal (Real.exp (-(t * m))) * ENNReal.ofReal (Real.exp (t * m + K)) :=
          mul_le_mul_right hb _
      _ = ENNReal.ofReal (Real.exp K) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1
          ring
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos K).le).mp hmain

private theorem aux_mcdiarmid_18 {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) :
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ)
      ≤ Real.exp (t ^ 2 * (∑ j, c j ^ 2) / 8) := by
  have hb := aux_mcdiarmid_18_g μ f hf B hB c hc hbd t
  exact aux_mcdiarmid_18_main (Measure.pi μ) f hf B hB t (∫ y, f y ∂(Measure.pi μ))
    (t ^ 2 * (∑ j, c j ^ 2) / 8) hb


-- |∫ f| ≤ B: norm_integral_le_of_norm_le_const (bound ae_of_all from hB, Real.norm_eq_abs),
-- then probReal_univ / measureReal_univ_eq_one and mul_one.
private theorem aux_mcdiarmid_19_1 {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (B : ℝ) (hB : ∀ x, |f x| ≤ B) : |∫ y, f y ∂ν| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := f) (C := B)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  simpa [Real.norm_eq_abs] using h

-- Integrability of exp(t (f - m)) for bounded measurable f and |m| ≤ B:
-- Integrable.of_bound (((hf.sub_const m).const_mul t).exp.aestronglyMeasurable) with bound
-- exp(|t| (2B)); Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp, le_abs_self,
-- abs_mul, abs_sub ≤ |f x| + |m| (abs_sub), mul_le_mul_of_nonneg_left.
private theorem aux_mcdiarmid_19_2 {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (B m : ℝ) (hB : ∀ x, |f x| ≤ B) (hm : |m| ≤ B) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (f x - m))) ν := by
  refine Integrable.of_bound (((hf.sub_const m).const_mul t).exp.aestronglyMeasurable)
    (Real.exp (|t| * (2 * B))) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (abs_nonneg t)
  linarith [hB x]

-- mgf_le in the target proxy: unfold ProbabilityTheory.mgf; aux_mcdiarmid_18 gives the bound
-- exp(t² S/8); the proxy coerces by Real.coe_toNNReal _ (div_nonneg (Finset.sum_nonneg …) (by norm_num))
-- and S/4 · t²/2 = t² S/8 (ring).
private theorem aux_mcdiarmid_19_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) (t : ℝ) :
    mgf (fun x => f x - ∫ y, f y ∂(Measure.pi μ)) (Measure.pi μ) t
      ≤ Real.exp (((Real.toNNReal ((∑ i, c i ^ 2) / 4) : NNReal) : ℝ) * t ^ 2 / 2) := by
  have hS : 0 ≤ (∑ i, c i ^ 2) / 4 := div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)
  rw [Real.coe_toNNReal _ hS]
  unfold mgf
  exact (aux_mcdiarmid_18 μ f hf B hB c hc hbd t).trans (le_of_eq (by ring_nf))

-- Build the structure: integrable_exp_mul t := Integrable.of_bound (measurability by fun_prop /
-- (hf.sub_const _).const_mul _ |>.exp) with bound exp(|t| * 2B) (Real.exp_le_exp, abs_le);
-- mgf_le t := by unfold ProbabilityTheory.mgf; simpa/convert aux_mcdiarmid_18 with
-- Real.coe_toNNReal _ (by positivity) and ring_nf on exponents (S/4 * t²/2 = t² S/8).
private theorem aux_mcdiarmid_19 {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂(Measure.pi μ))
      (Real.toNNReal ((∑ i, c i ^ 2) / 4)) (Measure.pi μ) := by
  exact ⟨fun t => aux_mcdiarmid_19_2 (Measure.pi μ) f hf B _ hB
      (aux_mcdiarmid_19_1 (Measure.pi μ) f B hB) t,
    fun t => aux_mcdiarmid_19_3 μ f hf B hB c hc hbd t⟩

-- Real algebra incl. the junk case S = 0 (both sides are -…/0 = 0): by_cases hS : S = 0;
-- simp [hS]; otherwise field_simp; ring.
private theorem aux_mcdiarmid_20 (S t : ℝ) (hS : 0 ≤ S) :
    -t ^ 2 / (2 * ((Real.toNNReal (S / 4) : NNReal) : ℝ)) = -2 * t ^ 2 / S := by
  by_cases hS0 : S = 0
  · subst hS0
    simp
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have h4 : ((Real.toNNReal (S / 4) : NNReal) : ℝ) = S / 4 :=
      Real.coe_toNNReal _ (by linarith)
    rw [h4]
    rw [div_eq_div_iff (by intro h; linarith) (by intro h; exact hS0 h)]
    ring


end McDiarmidAux

open McDiarmidAux in
/-- McDiarmid's inequality for a finite product of probability spaces. -/
theorem mcdiarmid {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (hf : Measurable f) (c : ι → ℝ)
    (hbd : ∀ (i : ι) (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | t ≤ f x - ∫ y, f y ∂(Measure.pi μ)}
      ≤ Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by
  haveI : ∀ i, Nonempty (Ω i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  have hc : ∀ i, 0 ≤ c i := aux_mcdiarmid_2 f c hbd
  obtain ⟨B, hB⟩ := aux_mcdiarmid_3 f c hbd
  have hsg := aux_mcdiarmid_19 μ f hf B hB c hc hbd
  have h := hsg.measure_ge_le ht
  rwa [aux_mcdiarmid_20 _ t (Finset.sum_nonneg fun i _ => sq_nonneg (c i))] at h

end LatticeProb
