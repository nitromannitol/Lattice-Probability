import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The largest square of a family with mass at most `m`

Let `𝒟` be a family of subsets of a type `E` (the squares of a dyadic system of the plane), let
`ν : Set E → ℝ≥0∞` be a mass function (for a cell configuration `H`, the mass of a square `S` is
`∑_{H ∈ H(S)} Area(H ∩ S) / Area(H)`), and let `m : ℝ≥0∞`. Following Gwynne, Miller and Sheffield
(*An invariance principle for ergodic scale-free random environments*, arXiv 1807.07515, (2.1)),
the square `Ŝ_m^w` is the largest square of `𝒟` that contains `w` and has mass at most `m`.

We define `cappedSquare 𝒟 ν m w` as the union of the candidate squares (the squares of `𝒟` that
contain `w` and have mass at most `m`); no choice is involved, and when a largest candidate exists
(`IsCappedSquare`, i.e. `IsGreatest` for inclusion) the union is that candidate
(`IsCappedSquare.cappedSquare_eq`).

## Main statements

* `LatticeProb.CappedSquare.cappedSquare_image`, `isCappedSquare_image`: covariance under an
  injective map `T` when the mass is transported, `ν' (T '' S) = ν S` (for a similarity of the plane
  and the mass of a cell configuration, area ratios are invariant).
* `LatticeProb.CappedSquare.IsCappedSquare.of_mem_interior`: for a nested family of squares (two
  squares are nested or have disjoint interiors) each contained in the closure of its interior,
  `Ŝ_m^w = Ŝ_m^z` whenever `w` lies in the interior of `Ŝ_m^z` (IP Lemma 2.2, second part).
* `LatticeProb.CappedSquare.isCappedSquare_chain_iff`, `exists_isCappedSquare_chain`: when the
  squares containing `w` form a chain `C : ℤ → Set E` along which the mass is strictly increasing,
  `C j = Ŝ_m^w` exactly for `m` in the nonempty interval `[ν (C j), ν (C (j + 1)))`, which lies in
  `(0, ∞)` (IP Lemma 2.2, first part), and some `C j` is `Ŝ_m^w` as soon as the mass of the chain
  is at most `m` somewhere and exceeds `m` somewhere.
-/

open Set Function
open scoped ENNReal

namespace LatticeProb.CappedSquare

variable {E F : Type*}

/-- The candidate squares for `Ŝ_m^w`: the members of `𝒟` that contain `w` and have mass at most
`m`. -/
def candidates (𝒟 : Set (Set E)) (ν : Set E → ℝ≥0∞) (m : ℝ≥0∞) (w : E) : Set (Set E) :=
  {S | S ∈ 𝒟 ∧ w ∈ S ∧ ν S ≤ m}

theorem mem_candidates {𝒟 : Set (Set E)} {ν : Set E → ℝ≥0∞} {m : ℝ≥0∞} {w : E} {S : Set E} :
    S ∈ candidates 𝒟 ν m w ↔ S ∈ 𝒟 ∧ w ∈ S ∧ ν S ≤ m :=
  Iff.rfl

/-- The square `Ŝ_m^w` of IP (2.1), defined as the union of the candidate squares; it is the
largest candidate when one exists (`IsCappedSquare.cappedSquare_eq`). -/
def cappedSquare (𝒟 : Set (Set E)) (ν : Set E → ℝ≥0∞) (m : ℝ≥0∞) (w : E) : Set E :=
  ⋃₀ candidates 𝒟 ν m w

/-- `S` is the largest square of `𝒟` that contains `w` and has mass at most `m`. -/
def IsCappedSquare (𝒟 : Set (Set E)) (ν : Set E → ℝ≥0∞) (m : ℝ≥0∞) (w : E) (S : Set E) : Prop :=
  IsGreatest (candidates 𝒟 ν m w) S

variable {𝒟 : Set (Set E)} {ν : Set E → ℝ≥0∞} {m : ℝ≥0∞} {w z : E} {S S' : Set E}

theorem IsCappedSquare.mem_family (h : IsCappedSquare 𝒟 ν m w S) : S ∈ 𝒟 :=
  h.1.1

theorem IsCappedSquare.mem (h : IsCappedSquare 𝒟 ν m w S) : w ∈ S :=
  h.1.2.1

theorem IsCappedSquare.mass_le (h : IsCappedSquare 𝒟 ν m w S) : ν S ≤ m :=
  h.1.2.2

theorem IsCappedSquare.subset (h : IsCappedSquare 𝒟 ν m w S) (hS' : S' ∈ 𝒟) (hw : w ∈ S')
    (hm : ν S' ≤ m) : S' ⊆ S :=
  h.2 ⟨hS', hw, hm⟩

theorem IsCappedSquare.unique (h : IsCappedSquare 𝒟 ν m w S) (h' : IsCappedSquare 𝒟 ν m w S') :
    S = S' :=
  IsGreatest.unique h h'

theorem IsCappedSquare.cappedSquare_eq (h : IsCappedSquare 𝒟 ν m w S) :
    cappedSquare 𝒟 ν m w = S := by
  rw [cappedSquare, ← Set.sSup_eq_sUnion]
  exact h.isLUB.sSup_eq

theorem isCappedSquare_cappedSquare (h : IsCappedSquare 𝒟 ν m w S) :
    IsCappedSquare 𝒟 ν m w (cappedSquare 𝒟 ν m w) := by
  rw [h.cappedSquare_eq]
  exact h

theorem mem_cappedSquare_of_isCappedSquare (h : IsCappedSquare 𝒟 ν m w S) :
    w ∈ cappedSquare 𝒟 ν m w := by
  rw [h.cappedSquare_eq]
  exact h.mem

/-! ### Covariance -/

theorem candidates_image {T : E → F} (hT : Injective T) {ν' : Set F → ℝ≥0∞}
    (hν : ∀ S ∈ 𝒟, ν' (T '' S) = ν S) (m : ℝ≥0∞) (w : E) :
    candidates (image T '' 𝒟) ν' m (T w) = image T '' candidates 𝒟 ν m w := by
  ext S'
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, hw, hm⟩
    exact ⟨S, ⟨hS, hT.mem_set_image.1 hw, hν S hS ▸ hm⟩, rfl⟩
  · rintro ⟨S, ⟨hS, hw, hm⟩, rfl⟩
    exact ⟨⟨S, hS, rfl⟩, mem_image_of_mem T hw, (hν S hS).symm ▸ hm⟩

/-- Covariance of `Ŝ_m^w`: `Ŝ_m^{T w}(T 𝒟, ν') = T (Ŝ_m^w(𝒟, ν))` for an injective `T`
transporting the mass. -/
theorem cappedSquare_image {T : E → F} (hT : Injective T) {ν' : Set F → ℝ≥0∞}
    (hν : ∀ S ∈ 𝒟, ν' (T '' S) = ν S) (m : ℝ≥0∞) (w : E) :
    cappedSquare (image T '' 𝒟) ν' m (T w) = T '' cappedSquare 𝒟 ν m w := by
  simp only [cappedSquare, candidates_image hT hν, sUnion_image, image_sUnion]

theorem isCappedSquare_image {T : E → F} (hT : Injective T) {ν' : Set F → ℝ≥0∞}
    (hν : ∀ S ∈ 𝒟, ν' (T '' S) = ν S) (m : ℝ≥0∞) (w : E) (S : Set E) :
    IsCappedSquare (image T '' 𝒟) ν' m (T w) (T '' S) ↔ IsCappedSquare 𝒟 ν m w S := by
  rw [IsCappedSquare, IsCappedSquare, candidates_image hT hν]
  constructor
  · rintro ⟨⟨S₀, hS₀, hS₀eq⟩, hub⟩
    refine ⟨(image_injective.2 hT hS₀eq) ▸ hS₀, fun S' hS' => ?_⟩
    exact (image_subset_image_iff hT).1 (hub ⟨S', hS', rfl⟩)
  · rintro ⟨hS, hub⟩
    refine ⟨⟨S, hS, rfl⟩, ?_⟩
    rintro _ ⟨S', hS', rfl⟩
    exact fun x ⟨y, hy, hyx⟩ => ⟨y, hub hS' hy, hyx⟩

/-! ### Lemma 2.2: interior points and chains -/

/-- IP Lemma 2.2, second part: in a nested family of squares (two squares are nested or have
disjoint interiors), each contained in the closure of its interior, the largest square of mass at
most `m` containing `z` is also the largest one containing any point `w` of its interior. -/
theorem IsCappedSquare.of_mem_interior [TopologicalSpace E]
    (hnest : ∀ S ∈ 𝒟, ∀ S' ∈ 𝒟, S ⊆ S' ∨ S' ⊆ S ∨ Disjoint (interior S) (interior S'))
    (hcl : ∀ S ∈ 𝒟, S ⊆ closure (interior S)) (h : IsCappedSquare 𝒟 ν m z S)
    (hw : w ∈ interior S) : IsCappedSquare 𝒟 ν m w S := by
  refine ⟨⟨h.mem_family, interior_subset hw, h.mass_le⟩, ?_⟩
  rintro S' ⟨hS', hwS', hm'⟩
  rcases hnest S h.mem_family S' hS' with hSS' | hS'S | hdisj
  · exact h.subset hS' (hSS' h.mem) hm'
  · exact hS'S
  · obtain ⟨x, hxS, hxS'⟩ :=
      mem_closure_iff.1 (hcl S' hS' hwS') (interior S) isOpen_interior hw
    exact absurd hxS' (disjoint_left.1 hdisj hxS)

theorem cappedSquare_eq_of_mem_interior [TopologicalSpace E]
    (hnest : ∀ S ∈ 𝒟, ∀ S' ∈ 𝒟, S ⊆ S' ∨ S' ⊆ S ∨ Disjoint (interior S) (interior S'))
    (hcl : ∀ S ∈ 𝒟, S ⊆ closure (interior S)) (h : IsCappedSquare 𝒟 ν m z S)
    (hw : w ∈ interior (cappedSquare 𝒟 ν m z)) :
    cappedSquare 𝒟 ν m w = cappedSquare 𝒟 ν m z := by
  rw [h.cappedSquare_eq] at hw ⊢
  exact (h.of_mem_interior hnest hcl hw).cappedSquare_eq

section Chain

variable {C : ℤ → Set E}

/-- If the squares of `𝒟` containing `w` form a monotone chain `C` along which the mass is
monotone, then `C j` is `Ŝ_m^w` as soon as `ν (C j) ≤ m < ν (C (j + 1))`. -/
theorem isCappedSquare_chain (hC : Monotone C) (hCmem : ∀ j, C j ∈ 𝒟) (hw : ∀ j, w ∈ C j)
    (hall : ∀ S ∈ 𝒟, w ∈ S → ∃ j, S = C j) (hν : Monotone (ν ∘ C)) {j : ℤ}
    (hj : ν (C j) ≤ m) (hj' : m < ν (C (j + 1))) : IsCappedSquare 𝒟 ν m w (C j) := by
  refine ⟨⟨hCmem j, hw j, hj⟩, ?_⟩
  rintro S ⟨hS, hwS, hm⟩
  obtain ⟨i, rfl⟩ := hall S hS hwS
  rcases le_or_gt i j with hij | hji
  · exact hC hij
  · exact absurd ((hν (Int.add_one_le_iff.2 hji : j + 1 ≤ i)).trans hm) (not_le.2 hj')

/-- Existence of `Ŝ_m^w` along a chain: if the mass of the chain is at most `m` at some index
and exceeds `m` at some index, then a largest square of mass at most `m` containing `w` exists. -/
theorem exists_isCappedSquare_chain (hC : Monotone C) (hCmem : ∀ j, C j ∈ 𝒟)
    (hw : ∀ j, w ∈ C j) (hall : ∀ S ∈ 𝒟, w ∈ S → ∃ j, S = C j) (hν : Monotone (ν ∘ C))
    (hlow : ∃ j, ν (C j) ≤ m) (hhigh : ∃ j, m < ν (C j)) :
    ∃ j, ν (C j) ≤ m ∧ m < ν (C (j + 1)) ∧ IsCappedSquare 𝒟 ν m w (C j) := by
  classical
  obtain ⟨b, hb⟩ := hhigh
  have hbdd : ∃ b' : ℤ, ∀ i, ν (C i) ≤ m → i ≤ b' := by
    refine ⟨b, fun i hi => ?_⟩
    by_contra hbi
    exact absurd ((hν (le_of_lt (not_le.1 hbi))).trans hi) (not_le.2 hb)
  obtain ⟨J, hJ, hJmax⟩ := Int.exists_greatest_of_bdd hbdd hlow
  have hJ' : m < ν (C (J + 1)) := by
    by_contra hle
    have := hJmax (J + 1) (not_lt.1 hle)
    omega
  exact ⟨J, hJ, hJ', isCappedSquare_chain hC hCmem hw hall hν hJ hJ'⟩

/-- IP Lemma 2.2, first part: if the squares of `𝒟` containing `w` form a monotone chain `C`
along which the mass is strictly increasing, then `C j = Ŝ_m^w` exactly for `m` in the interval
`[ν (C j), ν (C (j + 1)))`. -/
theorem isCappedSquare_chain_iff (hC : Monotone C) (hCmem : ∀ j, C j ∈ 𝒟) (hw : ∀ j, w ∈ C j)
    (hall : ∀ S ∈ 𝒟, w ∈ S → ∃ j, S = C j) (hν : StrictMono (ν ∘ C)) (j : ℤ) :
    IsCappedSquare 𝒟 ν m w (C j) ↔ m ∈ Ico (ν (C j)) (ν (C (j + 1))) := by
  constructor
  · intro h
    refine ⟨h.mass_le, ?_⟩
    by_contra hle
    have hsub : C (j + 1) ⊆ C j := h.subset (hCmem (j + 1)) (hw (j + 1)) (not_lt.1 hle)
    have heq : C (j + 1) = C j := le_antisymm hsub (hC (by omega : j ≤ j + 1))
    have hlt : ν (C j) < ν (C (j + 1)) := hν (by omega : j < j + 1)
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨hj, hj'⟩
    exact isCappedSquare_chain hC hCmem hw hall hν.monotone hj hj'

/-- The interval of masses `m` for which `C j = Ŝ_m^w` is a nonempty subinterval of `(0, ∞)`. -/
theorem nonempty_Ico_chain (hν : StrictMono (ν ∘ C)) (j : ℤ) :
    (Ico (ν (C j)) (ν (C (j + 1)))).Nonempty :=
  nonempty_Ico.2 (hν (by omega : j < j + 1))

theorem Ico_chain_subset_Ioo (hν : StrictMono (ν ∘ C)) (j : ℤ) :
    Ico (ν (C j)) (ν (C (j + 1))) ⊆ Ioo 0 ∞ := by
  have h0 : 0 < ν (C j) := zero_le.trans_lt (hν (by omega : j - 1 < j) : ν (C (j - 1)) < ν (C j))
  have htop : ν (C (j + 1)) < ∞ :=
    (hν (by omega : j + 1 < j + 1 + 1) : ν (C (j + 1)) < ν (C (j + 1 + 1))).trans_le le_top
  rintro x ⟨hx, hx'⟩
  exact ⟨h0.trans_le hx, hx'.trans htop⟩

end Chain

end LatticeProb.CappedSquare
