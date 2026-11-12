/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.Dyadic at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic

/-!
# DFGPS.D2.4: dyadic squares and dyadic domains

DFGPS Definition 2.4 (`literature/src/1905.00380/lqg-metric-estimates-final.tex` l. 810–813):
"A closed square `S ⊂ ℂ` is dyadic if `S` has side length `2^k` and corners in `2^k ℤ²` for some
`k ∈ ℤ`. We say that `W ⊂ ℂ` is a dyadic domain if there exists a finite collection of dyadic
squares `𝒮` such that `W` is the interior of `⋃_{S ∈ 𝒮} S`. Note that a dyadic domain is a
bounded open set." The class `𝒲` of dyadic domains is countable (used in DFGPS Lemma 2.5).
(The blueprint's `M2Defs.dyadicSq` has levels `n ∈ ℕ`, side `2^{-n}`, only; DFGPS allow all
`k ∈ ℤ`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace LFPP

/-- the closed dyadic square of side `2^k` with lower-left corner `2^k j` -/
def dfDyadicSq (k : ℤ) (j : ℤ × ℤ) : Set ℂ :=
  {x | (j.1 : ℝ) * 2 ^ k ≤ x.re ∧ x.re ≤ ((j.1 : ℝ) + 1) * 2 ^ k ∧
    (j.2 : ℝ) * 2 ^ k ≤ x.im ∧ x.im ≤ ((j.2 : ℝ) + 1) * 2 ^ k}

/-- `S` is a dyadic square (DFGPS Def. 2.4) -/
def IsDyadicSquare (S : Set ℂ) : Prop := ∃ (k : ℤ) (j : ℤ × ℤ), S = dfDyadicSq k j

/-- the dyadic domain of a finite collection of dyadic squares (indexed by `(k, j)`) -/
def dyadicDomainOf (F : Finset (ℤ × ℤ × ℤ)) : Set ℂ :=
  interior (⋃ p ∈ F, dfDyadicSq p.1 p.2)

/-- `W` is a dyadic domain (DFGPS Def. 2.4) -/
def IsDyadicDomain (W : Set ℂ) : Prop :=
  ∃ 𝒮 : Finset (Set ℂ), (∀ S ∈ 𝒮, IsDyadicSquare S) ∧ W = interior (⋃ S ∈ 𝒮, S)

/-- the class `𝒲` of dyadic domains -/
def dyadicDomains : Set (Set ℂ) := {W | IsDyadicDomain W}

theorem isCompact_dfDyadicSq (k : ℤ) (j : ℤ × ℤ) : IsCompact (dfDyadicSq k j) := by
  have : dfDyadicSq k j = Complex.equivRealProdCLM.symm ''
      (Icc ((j.1 : ℝ) * 2 ^ k) (((j.1 : ℝ) + 1) * 2 ^ k) ×ˢ
        Icc ((j.2 : ℝ) * 2 ^ k) (((j.2 : ℝ) + 1) * 2 ^ k)) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x.re, x.im), ⟨⟨hx.1, hx.2.1⟩, hx.2.2.1, hx.2.2.2⟩, by apply Complex.ext <;> simp⟩
    · rintro ⟨p, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
      simp only [dfDyadicSq, mem_ofPred_eq]
      simp only [Complex.equivRealProdCLM_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im]
      exact ⟨h1, h2, h3, h4⟩
  rw [this]
  exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

/-- a dyadic domain is open -/
theorem IsDyadicDomain.isOpen {W : Set ℂ} (hW : IsDyadicDomain W) : IsOpen W := by
  obtain ⟨𝒮, -, rfl⟩ := hW
  exact isOpen_interior

/-- a dyadic domain is bounded -/
theorem IsDyadicDomain.isBounded {W : Set ℂ} (hW : IsDyadicDomain W) :
    Bornology.IsBounded W := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := hW
  refine Bornology.IsBounded.subset ?_ interior_subset
  refine (Bornology.isBounded_biUnion_finset 𝒮).2 fun S hS => ?_
  obtain ⟨k, j, rfl⟩ := h𝒮 S hS
  exact (isCompact_dfDyadicSq k j).isBounded

theorem isDyadicDomain_iff {W : Set ℂ} :
    IsDyadicDomain W ↔ ∃ F : Finset (ℤ × ℤ × ℤ), W = dyadicDomainOf F := by
  classical
  constructor
  · rintro ⟨𝒮, h𝒮, rfl⟩
    choose k j hkj using h𝒮
    refine ⟨𝒮.attach.image fun S => (k S.1 S.2, j S.1 S.2), ?_⟩
    simp only [dyadicDomainOf]
    congr 1
    ext x
    simp only [mem_iUnion, Finset.mem_image, Finset.mem_attach, true_and, exists_prop]
    constructor
    · rintro ⟨S, hS, hx⟩
      exact ⟨_, ⟨⟨S, hS⟩, rfl⟩, by rw [← hkj S hS]; exact hx⟩
    · rintro ⟨p, ⟨⟨S, hS⟩, rfl⟩, hx⟩
      exact ⟨S, hS, by rw [hkj S hS]; exact hx⟩
  · rintro ⟨F, rfl⟩
    refine ⟨F.image fun p => dfDyadicSq p.1 p.2, ?_, ?_⟩
    · intro S hS
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hS
      exact ⟨p.1, p.2, rfl⟩
    · simp only [dyadicDomainOf]
      congr 1
      ext x
      simp only [mem_iUnion, Finset.mem_image, exists_prop]
      constructor
      · rintro ⟨p, hp, hx⟩; exact ⟨_, ⟨p, hp, rfl⟩, hx⟩
      · rintro ⟨S, ⟨p, hp, rfl⟩, hx⟩; exact ⟨p, hp, hx⟩

/-- **the class `𝒲` of dyadic domains is countable** -/
theorem dyadicDomains_countable : dyadicDomains.Countable := by
  have : dyadicDomains = range dyadicDomainOf := by
    ext W
    simp only [dyadicDomains, mem_ofPred_eq, mem_range, isDyadicDomain_iff, eq_comm]
  rw [this]
  exact countable_range _

end LFPP
end LQGMetric
