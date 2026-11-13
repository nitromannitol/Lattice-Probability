/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ReverseRationalMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ReverseConditionalMaximal
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Finset.Sort

/-! Weak-type (1,1) maximal control for conditional expectations along a
*decreasing family of sub-sigma-fields indexed by the rationals*.

This is the rational-parameter extension of the integer statement
`ReflectedGMS.ReverseConditional.measure_exists_lt_abs_condExp_le`, which is the
step `\eqref{p:eq:rationalmax}` in the complete dyadic-chain convergence lemma:
the rational-parameter averages `A_m` obey

  `P[sup_{m ∈ ℚ, m ≥ n} |A_m - L| > δ] ≤ E|A_n - L| / δ`.

The proof reduces to the integer case exactly as in the manuscript: a *finite*
list of rational parameters is sorted increasingly (so that the corresponding
sub-sigma-fields are decreasing) and extended by its last entry to an honest
`ℕ`-indexed antitone family, to which the integer reverse maximal inequality
applies; the finite lists are then increased along an enumeration of `ℚ` and
continuity of the measure from below gives the full rational supremum.

No reverse convergence statement is assumed or proved here; only the maximal
estimate for an arbitrary integrable error function. -/

set_option autoImplicit false

open MeasureTheory Filter

namespace ReflectedGMS.ReverseConditional

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Any nonempty finite set of rationals is covered by the range of a monotone
`ℕ`-indexed sequence: enumerate it increasingly and hold the value at its
maximum from its cardinality on. -/
theorem exists_monotone_enum_of_finset (S : Finset ℚ) (hS : S.Nonempty) :
    ∃ g : ℕ → ℚ, Monotone g ∧ ∀ q ∈ S, ∃ k, g k = q := by
  have hcard : 0 < S.card := Finset.card_pos.2 hS
  have hlt : ∀ k : ℕ, min k (S.card - 1) < S.card := fun k =>
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hcard Nat.one_pos)
  refine ⟨fun k => S.orderEmbOfFin rfl ⟨min k (S.card - 1), hlt k⟩, ?_, ?_⟩
  · intro i j hij
    exact (S.orderEmbOfFin rfl).monotone (Fin.mk_le_mk.2 (min_le_min hij le_rfl))
  · intro q hq
    have hmem : q ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      simpa using hq
    obtain ⟨i, hi⟩ := hmem
    refine ⟨(i : ℕ), ?_⟩
    have hfin : (⟨min (i : ℕ) (S.card - 1), hlt (i : ℕ)⟩ : Fin S.card) = i :=
      Fin.val_injective (min_eq_left (Nat.le_sub_one_of_lt i.isLt))
    simp only [hfin]
    exact hi

/-- Finite rational maximal inequality: for a decreasing family of
sub-sigma-fields indexed by `ℚ` and a finite set `S` of parameters, the
conditional expectations of an integrable `h` exceed the level `a > 0` in
absolute value at some parameter of `S` with probability at most `(∫ |h|)/a`. -/
theorem measure_exists_mem_finset_lt_abs_condExp_le {P : Measure Ω}
    [IsFiniteMeasure P] {ms : ℚ → MeasurableSpace Ω} (hanti : Antitone ms)
    (hle : ∀ q, ms q ≤ m0) (h : Ω → ℝ) {a : ℝ} (ha : 0 < a) (S : Finset ℚ) :
    P {ω | ∃ q ∈ S, a < |P[h | ms q] ω|} ≤
      ENNReal.ofReal ((∫ ω, |h ω| ∂P) / a) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨g, hgmono, hcover⟩ := exists_monotone_enum_of_finset S hS
  have hganti : Antitone fun k => ms (g k) := fun i j hij => hanti (hgmono hij)
  refine le_trans (measure_mono ?_)
    (measure_exists_lt_abs_condExp_le hganti (fun k => hle (g k)) h ha)
  rintro ω ⟨q, hq, hqlt⟩
  obtain ⟨k, hk⟩ := hcover q hq
  exact ⟨k, by rw [hk]; exact hqlt⟩

/-- Reverse weak-`L¹` maximal inequality over *all* rational parameters: along a
decreasing family of sub-sigma-fields indexed by `ℚ`, the conditional
expectations of an integrable `h` exceed the level `a > 0` in absolute value,
for some rational index, with probability at most `(∫ |h|)/a`. -/
theorem measure_exists_rat_lt_abs_condExp_le {P : Measure Ω} [IsFiniteMeasure P]
    {ms : ℚ → MeasurableSpace Ω} (hanti : Antitone ms) (hle : ∀ q, ms q ≤ m0)
    (h : Ω → ℝ) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ q : ℚ, a < |P[h | ms q] ω|} ≤
      ENNReal.ofReal ((∫ ω, |h ω| ∂P) / a) := by
  have hSmono : ∀ i j : ℕ, i ≤ j →
      (Finset.range (i + 1)).image (Denumerable.ofNat ℚ) ⊆
        (Finset.range (j + 1)).image (Denumerable.ofNat ℚ) := fun i j hij =>
    Finset.image_subset_image
      (Finset.range_subset.2 fun x hx => Finset.mem_range.2 (by omega))
  have hmono : Monotone fun N : ℕ => {ω |
      ∃ q ∈ (Finset.range (N + 1)).image (Denumerable.ofNat ℚ),
        a < |P[h | ms q] ω|} := by
    rintro i j hij ω ⟨q, hq, hqlt⟩
    exact ⟨q, hSmono i j hij hq, hqlt⟩
  have hun : (⋃ N : ℕ, {ω |
      ∃ q ∈ (Finset.range (N + 1)).image (Denumerable.ofNat ℚ),
        a < |P[h | ms q] ω|}) = {ω | ∃ q : ℚ, a < |P[h | ms q] ω|} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, q, _, hqlt⟩
      exact ⟨q, hqlt⟩
    · rintro ⟨q, hqlt⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Denumerable.ofNat ℚ n = q :=
        ⟨_, Denumerable.ofNat_encode q⟩
      refine ⟨n, q, ?_, hqlt⟩
      exact Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_self _), hn⟩
  rw [← hun, hmono.measure_iUnion]
  exact iSup_le fun N =>
    measure_exists_mem_finset_lt_abs_condExp_le hanti hle h ha _

/-- The form used in the complete dyadic-chain convergence lemma: the supremum
is taken over the rational parameters beyond a fixed one. -/
theorem measure_exists_rat_ge_lt_abs_condExp_le {P : Measure Ω}
    [IsFiniteMeasure P] {ms : ℚ → MeasurableSpace Ω} (hanti : Antitone ms)
    (hle : ∀ q, ms q ≤ m0) (h : Ω → ℝ) {a : ℝ} (ha : 0 < a) (r : ℚ) :
    P {ω | ∃ q : ℚ, r ≤ q ∧ a < |P[h | ms q] ω|} ≤
      ENNReal.ofReal ((∫ ω, |h ω| ∂P) / a) := by
  refine le_trans (measure_mono ?_)
    (measure_exists_rat_lt_abs_condExp_le hanti hle h ha)
  rintro ω ⟨q, -, hqlt⟩
  exact ⟨q, hqlt⟩

end ReflectedGMS.ReverseConditional
