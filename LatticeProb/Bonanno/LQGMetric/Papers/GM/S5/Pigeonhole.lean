/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Pigeonhole at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Defs

/-!
# Pigeonhole for a finitely-valued random choice (task P2-M2L)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, l. 2976: "The
number of subsets of `𝓢_{ε_1 r}(B_{2r}(z))` is bounded above by a deterministic constant depending
only on `ε_1`. Consequently, we can choose `p_1` … and a deterministic `𝒦_r(z)` such that with
probability at least `p_1` …" (also l. 2912 for Lemma 5.5 and Step 3 of Lemma 5.8). No
measurability is needed: outer-measure subadditivity. Own elementary proof (P2-M2L-4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM

/-- If `P[E] ≥ q` and `X` takes values in a finite type with `N` elements, some fibre of `X` carries
`P[E ∩ {X = i}] ≥ q / N`. -/
theorem exists_fiber_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} [Fintype ι]
    [Nonempty ι] (E : Set Ω) (X : Ω → ι) {q : ℝ≥0∞} (hE : q ≤ P E) :
    ∃ i, q / Fintype.card ι ≤ P (E ∩ X ⁻¹' {i}) := by
  by_contra hne
  push Not at hne
  have hcover : E ⊆ ⋃ i, E ∩ X ⁻¹' {i} := fun ω hω => mem_iUnion.2 ⟨X ω, hω, rfl⟩
  have h1 : P E ≤ ∑ i, P (E ∩ X ⁻¹' {i}) :=
    (measure_mono hcover).trans (measure_iUnion_fintype_le _ _)
  have h2 : ∑ i, P (E ∩ X ⁻¹' {i}) < ∑ _i : ι, q / Fintype.card ι :=
    ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hne i
  have h3 : ∑ _i : ι, q / Fintype.card ι ≤ q := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_div_le
  exact absurd (hE.trans h1) (not_le.2 (h2.trans_le h3))

end LQGMetric.GM
