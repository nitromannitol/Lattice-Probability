import Mathlib

/-!
# Reconstruction of a continuous path from its ladder sets

For a path `X : ℝ → ℝ` and an anchor `a`, the *forward ladder set* of `X` from `a` is the set of times `t ≥ a` at
which `X` attains its running minimum from `a`, and the *backward ladder set* is the set of times `t ≤ a` at which
`X` attains its minimum over `[t, a]`. For a set `K ⊆ ℝ`, `excursionCount K s t ε` is the number `N_ε` of complementary
intervals of `K` in `[s, t]` (the connected components of `[s, t] \ K`) of length larger than `ε`.

For a standard Brownian motion `B` with `B 0 = 0` and `K` the ladder set of `B` from `0`, the excursion-count
representation of the local time of `B - inf B` at `0` (Lévy; Pitman–Yor, *A guide to Brownian motion and related
stochastic processes*, Section 7.3) reads `-inf_[0,t] B = lim_{ε ↓ 0} √(π ε / 2) N_ε(K, t)`. This file uses that
identity only as an explicit hypothesis on each path, each anchor and each direction, and proves the deterministic
reconstruction steps.

## Main results

* `sub_sInf_eq_of_forwardLadderSet_eq`, `sub_sInf_eq_of_backwardLadderSet_eq`: if the identity holds for `X` and for
  `Y` from the anchor `a` and their ladder sets from `a` coincide, then the drops of their running minima from `a`
  coincide.
* `sub_eq_sub_of_ladderSets_eq`: equal forward ladder sets from `a` and equal backward ladder sets from `b ≥ a` give
  equal increments `X b - X a = Y b - Y a` (the minimum point of `X` on `[a, b]` lies in both ladder sets).
* `eq_of_ladderSets_eq_of_dense`, `eq_of_ladderSets_eq`: for continuous paths, equal ladder sets from every anchor of
  a dense set (in particular every rational anchor) in both directions, together with the identity for every such
  anchor, give `X = Y` once `X` and `Y` agree at one time.
-/

set_option autoImplicit false

open Filter Set Topology

namespace LatticeProb.LadderSet

/-- The forward ladder set of `X` from the anchor `a`: the times `t ≥ a` at which `X` attains its running minimum
from `a`, that is `X t ≤ X s` for every `s ∈ [a, t]`. -/
def forwardLadderSet (X : ℝ → ℝ) (a : ℝ) : Set ℝ :=
  {t | a ≤ t ∧ ∀ s ∈ Icc a t, X t ≤ X s}

/-- The backward ladder set of `X` from the anchor `a`: the times `t ≤ a` at which `X` attains its minimum over
`[t, a]`, that is `X t ≤ X s` for every `s ∈ [t, a]`. -/
def backwardLadderSet (X : ℝ → ℝ) (a : ℝ) : Set ℝ :=
  {t | t ≤ a ∧ ∀ s ∈ Icc t a, X t ≤ X s}

/-- The complementary intervals of `K` in `[s, t]`: the connected components of `[s, t] \ K`. -/
def complementaryIntervals (K : Set ℝ) (s t : ℝ) : Set (Set ℝ) :=
  {C | ∃ x ∈ Icc s t \ K, connectedComponentIn (Icc s t \ K) x = C}

/-- The excursion count `N_ε`: the number of complementary intervals of `K` in `[s, t]` of length (diameter) larger
than `ε`. -/
noncomputable def excursionCount (K : Set ℝ) (s t ε : ℝ) : ℕ :=
  {C ∈ complementaryIntervals K s t | ε < Metric.diam C}.ncard

/-- At a forward ladder time `t` from `a`, the running minimum of `X` over `[a, t]` is `X t`. -/
theorem sInf_image_Icc_eq_of_mem_forwardLadderSet {X : ℝ → ℝ} {a t : ℝ}
    (ht : t ∈ forwardLadderSet X a) : sInf (X '' Icc a t) = X t := by
  refine IsLeast.csInf_eq ⟨⟨t, ⟨ht.1, le_rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact ht.2 s hs

/-- At a backward ladder time `t` from `a`, the minimum of `X` over `[t, a]` is `X t`. -/
theorem sInf_image_Icc_eq_of_mem_backwardLadderSet {X : ℝ → ℝ} {a t : ℝ}
    (ht : t ∈ backwardLadderSet X a) : sInf (X '' Icc t a) = X t := by
  refine IsLeast.csInf_eq ⟨⟨t, ⟨le_rfl, ht.1⟩, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact ht.2 s hs

/-- Reconstruction of the running minimum from the forward ladder set. If, for the paths `X` and `Y` and the anchor
`a`, the drop of the running minimum over `[a, t]` is the limit of `√(π ε / 2) N_ε` for the forward ladder set from
`a` (for every `t ≥ a`), and the two forward ladder sets from `a` coincide, then the drops coincide for every
`t ≥ a`. -/
theorem sub_sInf_eq_of_forwardLadderSet_eq {X Y : ℝ → ℝ} {a : ℝ}
    (hX : ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t))))
    (hY : ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet Y a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (Y a - sInf (Y '' Icc a t))))
    (hK : forwardLadderSet X a = forwardLadderSet Y a) {t : ℝ} (ht : a ≤ t) :
    X a - sInf (X '' Icc a t) = Y a - sInf (Y '' Icc a t) := by
  have hXt := hX t ht
  rw [hK] at hXt
  exact tendsto_nhds_unique hXt (hY t ht)

/-- Reconstruction of the running minimum from the backward ladder set. If, for the paths `X` and `Y` and the anchor
`b`, the drop of the minimum over `[t, b]` is the limit of `√(π ε / 2) N_ε` for the backward ladder set from `b`
(for every `t ≤ b`), and the two backward ladder sets from `b` coincide, then the drops coincide for every
`t ≤ b`. -/
theorem sub_sInf_eq_of_backwardLadderSet_eq {X Y : ℝ → ℝ} {b : ℝ}
    (hX : ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (X b - sInf (X '' Icc t b))))
    (hY : ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet Y b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (Y b - sInf (Y '' Icc t b))))
    (hK : backwardLadderSet X b = backwardLadderSet Y b) {t : ℝ} (ht : t ≤ b) :
    X b - sInf (X '' Icc t b) = Y b - sInf (Y '' Icc t b) := by
  have hXt := hX t ht
  rw [hK] at hXt
  exact tendsto_nhds_unique hXt (hY t ht)

/-- Equal increments between two anchors. Let `X` be continuous and `a ≤ b`. If the excursion-count identity holds
for `X` and `Y` forward from `a` and backward from `b`, and the forward ladder sets from `a` and the backward ladder
sets from `b` of `X` and `Y` coincide, then `X b - X a = Y b - Y a`. A minimum point `m` of `X` on `[a, b]` lies in
both ladder sets of `X`, hence of `Y`, so `X a - X m = Y a - Y m` and `X b - X m = Y b - Y m`. -/
theorem sub_eq_sub_of_ladderSets_eq {X Y : ℝ → ℝ} (hXc : Continuous X) {a b : ℝ} (hab : a ≤ b)
    (hXf : ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t))))
    (hYf : ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet Y a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (Y a - sInf (Y '' Icc a t))))
    (hXb : ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (X b - sInf (X '' Icc t b))))
    (hYb : ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet Y b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (Y b - sInf (Y '' Icc t b))))
    (hKf : forwardLadderSet X a = forwardLadderSet Y a)
    (hKb : backwardLadderSet X b = backwardLadderSet Y b) :
    X b - X a = Y b - Y a := by
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hXc.continuousOn
  have hmin' := isMinOn_iff.mp hmin
  have hmf : m ∈ forwardLadderSet X a :=
    ⟨hm.1, fun s hs => hmin' s ⟨hs.1, hs.2.trans hm.2⟩⟩
  have hmb : m ∈ backwardLadderSet X b :=
    ⟨hm.2, fun s hs => hmin' s ⟨hm.1.trans hs.1, hs.2⟩⟩
  have hmf' : m ∈ forwardLadderSet Y a := by
    rw [← hKf]
    exact hmf
  have hmb' : m ∈ backwardLadderSet Y b := by
    rw [← hKb]
    exact hmb
  have hf := sub_sInf_eq_of_forwardLadderSet_eq hXf hYf hKf hm.1
  have hb := sub_sInf_eq_of_backwardLadderSet_eq hXb hYb hKb hm.2
  rw [sInf_image_Icc_eq_of_mem_forwardLadderSet hmf,
    sInf_image_Icc_eq_of_mem_forwardLadderSet hmf'] at hf
  rw [sInf_image_Icc_eq_of_mem_backwardLadderSet hmb,
    sInf_image_Icc_eq_of_mem_backwardLadderSet hmb'] at hb
  linarith

/-- Equal ladder sets from a dense set of anchors give equal increments. For continuous `X` and `Y` such that, for
every anchor in a dense set `D` and in both directions, the excursion-count identity holds for `X` and for `Y` and
their ladder sets coincide, the difference `X - Y` is constant. -/
theorem sub_eq_sub_of_ladderSets_eq_of_dense {X Y : ℝ → ℝ} (hXc : Continuous X) (hYc : Continuous Y)
    {D : Set ℝ} (hD : Dense D)
    (hXf : ∀ a ∈ D, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t))))
    (hYf : ∀ a ∈ D, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet Y a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (Y a - sInf (Y '' Icc a t))))
    (hXb : ∀ b ∈ D, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (X b - sInf (X '' Icc t b))))
    (hYb : ∀ b ∈ D, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet Y b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (Y b - sInf (Y '' Icc t b))))
    (hKf : ∀ a ∈ D, forwardLadderSet X a = forwardLadderSet Y a)
    (hKb : ∀ b ∈ D, backwardLadderSet X b = backwardLadderSet Y b) (x y : ℝ) :
    X x - Y x = X y - Y y := by
  have hDD : ∀ a ∈ D, ∀ b ∈ D, X a - Y a = X b - Y b := by
    intro a ha b hb
    rcases le_total a b with hab | hba
    · have h := sub_eq_sub_of_ladderSets_eq hXc hab (hXf a ha) (hYf a ha) (hXb b hb) (hYb b hb)
        (hKf a ha) (hKb b hb)
      linarith
    · have h := sub_eq_sub_of_ladderSets_eq hXc hba (hXf b hb) (hYf b hb) (hXb a ha) (hYb a ha)
        (hKf b hb) (hKb a ha)
      linarith
  obtain ⟨d, hd⟩ := hD.nonempty
  have hconst : (fun z => X z - Y z) = fun _ => X d - Y d :=
    Continuous.ext_on hD (hXc.sub hYc) continuous_const (fun z hz => hDD z hz d hd)
  have hx : X x - Y x = X d - Y d := congrFun hconst x
  have hy : X y - Y y = X d - Y d := congrFun hconst y
  rw [hx, hy]

/-- Reconstruction of a continuous path from its ladder sets from a dense set of anchors. If, for every anchor in a
dense set `D` and in both directions, the excursion-count identity holds for `X` and for `Y` and their ladder sets
coincide, and `X t₀ = Y t₀` for one time `t₀`, then `X = Y`. -/
theorem eq_of_ladderSets_eq_of_dense {X Y : ℝ → ℝ} (hXc : Continuous X) (hYc : Continuous Y)
    {D : Set ℝ} (hD : Dense D)
    (hXf : ∀ a ∈ D, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t))))
    (hYf : ∀ a ∈ D, ∀ t, a ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet Y a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (Y a - sInf (Y '' Icc a t))))
    (hXb : ∀ b ∈ D, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (X b - sInf (X '' Icc t b))))
    (hYb : ∀ b ∈ D, ∀ t, t ≤ b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet Y b) t b ε : ℝ)) (𝓝[>] 0) (𝓝 (Y b - sInf (Y '' Icc t b))))
    (hKf : ∀ a ∈ D, forwardLadderSet X a = forwardLadderSet Y a)
    (hKb : ∀ b ∈ D, backwardLadderSet X b = backwardLadderSet Y b) {t₀ : ℝ} (h0 : X t₀ = Y t₀) :
    X = Y := by
  funext x
  have h := sub_eq_sub_of_ladderSets_eq_of_dense hXc hYc hD hXf hYf hXb hYb hKf hKb x t₀
  linarith

/-- Reconstruction of a continuous path from its ladder sets from the rational anchors. If, for every rational
anchor `q` and in both directions, the drop of the running minimum from `q` is the limit of `√(π ε / 2) N_ε` for the
ladder set from `q`, for `X` and for `Y`, and the ladder sets of `X` and `Y` from every rational anchor coincide,
then `X = Y` once `X 0 = Y 0`. -/
theorem eq_of_ladderSets_eq {X Y : ℝ → ℝ} (hXc : Continuous X) (hYc : Continuous Y)
    (hXf : ∀ q : ℚ, ∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X q) q t ε : ℝ)) (𝓝[>] 0) (𝓝 (X q - sInf (X '' Icc (q : ℝ) t))))
    (hYf : ∀ q : ℚ, ∀ t, (q : ℝ) ≤ t → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet Y q) q t ε : ℝ)) (𝓝[>] 0) (𝓝 (Y q - sInf (Y '' Icc (q : ℝ) t))))
    (hXb : ∀ q : ℚ, ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet X q) t q ε : ℝ)) (𝓝[>] 0) (𝓝 (X q - sInf (X '' Icc t (q : ℝ)))))
    (hYb : ∀ q : ℚ, ∀ t, t ≤ (q : ℝ) → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (backwardLadderSet Y q) t q ε : ℝ)) (𝓝[>] 0) (𝓝 (Y q - sInf (Y '' Icc t (q : ℝ)))))
    (hKf : ∀ q : ℚ, forwardLadderSet X q = forwardLadderSet Y q)
    (hKb : ∀ q : ℚ, backwardLadderSet X q = backwardLadderSet Y q) (h0 : X 0 = Y 0) :
    X = Y := by
  refine eq_of_ladderSets_eq_of_dense hXc hYc (D := Set.range ((↑) : ℚ → ℝ)) Rat.denseRange_cast
    ?_ ?_ ?_ ?_ ?_ ?_ h0
  all_goals rintro _ ⟨q, rfl⟩
  · exact hXf q
  · exact hYf q
  · exact hXb q
  · exact hYb q
  · exact hKf q
  · exact hKb q

end LatticeProb.LadderSet
