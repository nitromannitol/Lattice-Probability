/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Lemma46 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Localized

/-!
# The deterministic comparison in [18] Lemma 4.6

Source: [18] proof of Lemma 4.6 : with `N = deg^ε_in(z)` and intervals
`[a_j, b_j]`, "`η([τ_z − ε, τ_z + ε]) ⊂ H_{x−ε} ∪ H_x ∪ H_{x+ε}`, so for each `j` the segment `η([a_j, b_j])` intersects
either `H_{x−ε}`, `H_x`, or `H_{x+ε}` along a non-trivial boundary arc or at an interior point. Hence `η([a_j, b_j])`
intersects the interior of `H_y` for some `y` … equal to or connected by an edge in `G^ε` to one of `x − ε, x, x + ε`.
Since the intervals `[a_j, b_j]` intersect only at their endpoints and each has length `ε`, each such vertex `y` can
correspond to at most 2 of the intervals … Therefore `deg^ε_in(z) ≤ 2 Σ_{j=−1}^{1} deg(x^ε_z + jε; G^ε) + 6`."

**Finding (G4b).** The definition of `deg^ε_in` (`[18]`, and [20] Definition 4.5) only asks
`η([a_j, b_j]) ∩ η([τ_z − ε, τ_z + ε]) ≠ ∅`; the proof uses "contains a non-trivial connected set". With `≠ ∅`, two
cells may meet at a single (multiple) point without sharing a boundary arc, so the step "intersects … hence adjacent"
needs an extra cell-structure fact. This file proves the comparison with *intersecting* cells instead of adjacent ones,
which needs no cell structure:

* `locDegIn_le_three_mul_encard`: `deg^ε_in ≤ 3 #{k : H^ε_k ∩ η([t₀ − ε, t₀ + ε]) ≠ ∅}`;
* `locDegIn_le_cellIntersections`: `deg^ε_in ≤ 3 (#I(x − 1) + #I(x) + #I(x + 1))` with `I(m) = {k : H^ε_k ∩ H^ε_m ≠ ∅}`
  and `x = ⌈t₀/ε⌉` the cell of the root time.

The source's bound follows when intersecting cells are equal or adjacent in `G^ε` (e.g. when every intersection point
of two cells is a double point: DMS Lemmas 8.8, 8.14 with G0). Cells are `H^ε_k = η([ε(k − 1), εk])`, `k ∈ ℤ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- The cell `H^ε_k = c([ε(k − 1), εk])`. -/
def cellOf (ε : ℝ) (c : ℝ → ℂ) (k : ℤ) : Set ℂ := c '' Icc (ε * ((k : ℝ) - 1)) (ε * k)

/-- The cells meeting the local segment `c([t₀ − ε, t₀ + ε])`. -/
def windowCells (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) : Set ℤ :=
  {k | (cellOf ε c k ∩ locWindow ε c t₀).Nonempty}

/-- At most three pairwise disjoint open intervals of length `ε` fit into an open interval of length `3ε`. -/
theorem card_le_three_of_disjoint_Ioo {ι : Type*} {ε L : ℝ} (hε : 0 < ε) (s : Finset ι) (a : ι → ℝ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ioo (a i) (a i + ε)) (Ioo (a j) (a j + ε)))
    (hsub : ∀ i ∈ s, Ioo (a i) (a i + ε) ⊆ Ioo L (L + 3 * ε)) : s.card ≤ 3 := by
  have hU : volume (⋃ i ∈ s, Ioo (a i) (a i + ε)) = ∑ i ∈ s, volume (Ioo (a i) (a i + ε)) :=
    measure_biUnion_finset (fun i hi j hj hij => hd i hi j hj hij) (fun _ _ => measurableSet_Ioo)
  have hle : volume (⋃ i ∈ s, Ioo (a i) (a i + ε)) ≤ volume (Ioo L (L + 3 * ε)) :=
    measure_mono (iUnion₂_subset hsub)
  rw [hU] at hle
  simp only [Real.volume_Ioo, add_sub_cancel_left, Finset.sum_const, nsmul_eq_mul] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hle
  have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have : (s.card : ℝ) ≤ 3 := le_of_mul_le_mul_right (by linarith) hε
  exact_mod_cast this

/-- The cell index of a time: `t ∈ [ε(⌈t/ε⌉ − 1), ε⌈t/ε⌉]`. -/
theorem mem_Icc_ceil {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    t ∈ Icc (ε * (((⌈t / ε⌉ : ℤ) : ℝ) - 1)) (ε * ((⌈t / ε⌉ : ℤ) : ℝ)) := by
  have h1 := Int.ceil_lt_add_one (t / ε)
  have h2 := Int.le_ceil (t / ε)
  constructor
  · have : ((⌈t / ε⌉ : ℤ) : ℝ) - 1 ≤ t / ε := by linarith
    calc ε * (((⌈t / ε⌉ : ℤ) : ℝ) - 1) ≤ ε * (t / ε) := mul_le_mul_of_nonneg_left this hε.le
      _ = t := mul_div_cancel₀ t hε.ne'
  · calc t = ε * (t / ε) := (mul_div_cancel₀ t hε.ne').symm
      _ ≤ ε * ((⌈t / ε⌉ : ℤ) : ℝ) := mul_le_mul_of_nonneg_left h2 hε.le

/-- **Inner degree versus cells meeting the local segment.** `deg^ε_in ≤ 3 #{k : H^ε_k ∩ c([t₀ − ε, t₀ + ε]) ≠ ∅}`. -/
theorem locDegIn_le_three_mul_encard {ε : ℝ} (hε : 0 < ε) (c : ℝ → ℂ) (t₀ : ℝ) :
    locDegIn ε c t₀ ≤ 3 * (windowCells ε c t₀).encard := by
  refine locDegIn_le fun N a ha => ?_
  -- a time of each interval whose image lies in the local segment
  have hex : ∀ i, ∃ s ∈ Icc (a i) (a i + ε), c s ∈ locWindow ε c t₀ := by
    intro i
    obtain ⟨_, ⟨s, hs, rfl⟩, hw⟩ := (ha.2 i).2
    exact ⟨s, hs, hw⟩
  choose s hs hsw using hex
  set k : Fin N → ℤ := fun i => ⌈s i / ε⌉ with hk
  have hkmem : ∀ i, k i ∈ windowCells ε c t₀ := fun i =>
    ⟨c (s i), mem_image_of_mem c (mem_Icc_ceil hε (s i)), hsw i⟩
  have hfib : ∀ b ∈ (Finset.univ : Finset (Fin N)).image k,
      (Finset.univ.filter fun i => k i = b).card ≤ 3 := by
    intro b _
    refine card_le_three_of_disjoint_Ioo (L := ε * ((b : ℝ) - 2)) hε _ a
      (fun i _ j _ hij => ha.1 i j hij) fun i hi => ?_
    have hki : k i = b := (Finset.mem_filter.mp hi).2
    have hmem := mem_Icc_ceil hε (s i)
    rw [show ⌈s i / ε⌉ = k i from rfl, hki] at hmem
    intro x hx
    have h1 := (hs i).1
    have h2 := (hs i).2
    constructor
    · linarith [hmem.1, hx.1]
    · linarith [hmem.2, hx.2]
  have hcard := Finset.card_le_mul_card_image (Finset.univ : Finset (Fin N)) 3 hfib
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have himg : ((Finset.univ.image k : Finset ℤ) : Set ℤ) ⊆ windowCells ε c t₀ := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact hkmem i
  have henc : (((Finset.univ.image k).card : ℕ) : ℕ∞) ≤ (windowCells ε c t₀).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_le_encard himg
  calc (N : ℕ∞) ≤ ((3 * (Finset.univ.image k).card : ℕ) : ℕ∞) := by exact_mod_cast hcard
    _ = 3 * (((Finset.univ.image k).card : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ 3 * (windowCells ε c t₀).encard := by gcongr

end MatedCRTHarmonic.GMS4b
