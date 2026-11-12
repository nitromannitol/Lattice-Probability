/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.CrosscutTheta at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutSep

/-!
# Crosscuts, part IV: gluing separations, and the theta-curve separation for GM L4.13′

* `sep_glue`: compact `P, Q` and a compact connected `K` with `P ∩ Q ⊆ K`; if `P ∪ Q` separates
  `a, b` and `K ∪ Q` does not, then `K ∪ P` separates `a, b`.
* `theta_sep`: the separation core of GM (arXiv:1905.00383) Lemma 4.13 (`lem-geo-disconnect`),
  tex l. 2081 ("one of the connected components `V` of `ℂ ∖ (𝓑 ∪ X)` is bounded and contains an
  endpoint of `I`"): `K` compact connected with `ℂ ∖ K` and `int K` connected, `∂K ⊆ A ∪ B` with
  `A, B ⊆ ∂K` compact (the two closed arcs of the Jordan curve `∂K` between `p` and `q`),
  `X` compact connected (the closure of the crosscut) with `X ∩ K ⊆ A ∩ B ⊆ X` (it meets `K` only at
  `p, q`). A point `a ∉ K` near the `A`-side and a point `b ∉ K` near the `B`-side (each joined by a
  segment to a point of `int K` avoiding `X` and the other arc) are separated by `K ∪ X`.

**Proof.** `sep_glue` is Eilenberg's criterion with gluing of logarithms over the connected `K`
(as in the proof of Janiszewski's theorem, Burckel, *Classical Analysis in the Complex Plane*,
Ex. 4.37, printed p. 215; QuantumZipper `CA.Topo.janiszewski`). `theta_sep` applies it twice:
`A ∪ B ⊇ ∂K` separates `a` from `a' ∈ int K`, `X ∪ B` does not (segment), so `X ∪ A` separates
`a, a'`; `a' ~ b' ~ b` off `X ∪ A` (through `int K` and a segment), so `X ∪ A` separates `a, b`;
`K ∪ A = K` does not, so `K ∪ X` separates `a, b`. Own elementary route (no Jordan curve theorem,
no prime ends), recorded in `DEVIATIONS.md` (proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter Complex
open QuantumZipper.CA.Topo

namespace LQGMetric.Topo.Crosscut

/-- **Gluing separations** (Eilenberg's criterion; Burckel Ex. 4.37). -/
theorem sep_glue {K P Q : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hP : IsCompact P)
    (hQ : IsCompact Q) (hPQ : P ∩ Q ⊆ K) {a b : ℂ}
    (hsep : b ∉ connectedComponentIn (P ∪ Q)ᶜ a) (hQab : b ∈ connectedComponentIn (K ∪ Q)ᶜ a)
    (haP : a ∉ P) (hbP : b ∉ P) : b ∉ connectedComponentIn (K ∪ P)ᶜ a := by
  intro hb'
  obtain ⟨L1, hL1c, hL1⟩ := hasLogOn_of_not_separates (hK.union hQ) hQab
  obtain ⟨L2, hL2c, hL2⟩ := hasLogOn_of_not_separates (hK.union hP) hb'
  have haKQ : a ∉ K ∪ Q := connectedComponentIn_nonempty_iff.1 ⟨b, hQab⟩
  have hbKQ : b ∉ K ∪ Q := connectedComponentIn_subset _ _ hQab
  have hconst : ∀ {u v : ℂ}, u ∈ K → v ∈ K → L2 u - L1 u = L2 v - L1 v := fun hu hv =>
    QuantumZipper.JordanChord.log_sub_eq_of_isPreconnected hKc.isPreconnected
      (hL2c.mono subset_union_left) (hL1c.mono subset_union_left)
      (fun z hz => (hL2 z (Or.inl hz)).trans (hL1 z (Or.inl hz)).symm) hu hv
  obtain ⟨k₀, hk₀⟩ := hKc.nonempty
  set c₀ := L2 k₀ - L1 k₀
  have hc₀ : ∀ z ∈ K, L2 z = L1 z + c₀ := fun z hz => by
    have := hconst hz hk₀; simp only [c₀]; linear_combination this
  have hexp : Complex.exp c₀ = 1 := by
    have h1 : Complex.exp (L2 k₀) = (k₀ - a) / (k₀ - b) := hL2 k₀ (Or.inl hk₀)
    have h2 : Complex.exp (L1 k₀) = (k₀ - a) / (k₀ - b) := hL1 k₀ (Or.inl hk₀)
    have hf0 : (k₀ - a) / (k₀ - b) ≠ 0 :=
      div_ne_zero (sub_ne_zero.2 fun h => haKQ (Or.inl (h ▸ hk₀)))
        (sub_ne_zero.2 fun h => hbKQ (Or.inl (h ▸ hk₀)))
    simp only [c₀, Complex.exp_sub, h1, h2, div_self hf0]
  classical
  let L : ℂ → ℂ := fun z => if z ∈ P then L2 z else L1 z + c₀
  have hLc : ContinuousOn L (P ∪ Q) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hP.isClosed hQ.isClosed
    · exact (hL2c.mono subset_union_right).congr fun z hz => by simp [L, hz]
    · refine ((hL1c.mono subset_union_right).add (continuousOn_const (c := c₀))).congr
        fun z hz => ?_
      by_cases h : z ∈ P
      · simp only [L, h, ite_true]; exact hc₀ z (hPQ ⟨h, hz⟩)
      · simp [L, h]
  have hlog : HasLogOn (fun z => (z - a) / (z - b)) (P ∪ Q) := by
    refine ⟨L, hLc, fun z hz => ?_⟩
    by_cases h : z ∈ P
    · simp only [L, h, ite_true]; exact hL2 z (Or.inr h)
    · simp only [L, h, ite_false]; rw [Complex.exp_add, hexp, mul_one]
      exact hL1 z (Or.inr (hz.resolve_left h))
  exact hsep (not_separates_of_hasLogOn (hP.union hQ)
    (fun h => h.elim haP fun h' => haKQ (Or.inr h')) (fun h => h.elim hbP fun h' => hbKQ (Or.inr h'))
    hlog)

/-- A segment avoiding a closed set joins its ends in the complement. -/
theorem mem_cc_of_segment {S : Set ℂ} {a a' : ℂ} (h : segment ℝ a a' ⊆ Sᶜ) :
    a' ∈ connectedComponentIn Sᶜ a :=
  (convex_segment a a').isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ a a') h
    (right_mem_segment ℝ a a')

/-- **Theta-curve separation** (core of GM L4.13, tex l. 2081). -/
theorem theta_sep {K X A B : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) (hint : IsPreconnected (interior K)) (hX : IsCompact X)
    (hXc : IsConnected X) (hA : IsCompact A) (hB : IsCompact B) (hAK : A ⊆ frontier K)
    (hBK : B ⊆ frontier K) (hfr : frontier K ⊆ A ∪ B) (hXK : X ∩ K ⊆ A ∩ B) (hAB : A ∩ B ⊆ X)
    {a b a' b' : ℂ} (ha : a ∉ K) (hb : b ∉ K) (ha' : a' ∈ interior K) (hb' : b' ∈ interior K)
    (haa' : segment ℝ a a' ⊆ (X ∪ B)ᶜ) (hbb' : segment ℝ b b' ⊆ (X ∪ A)ᶜ) :
    b ∉ connectedComponentIn (K ∪ X)ᶜ a := by
  have hfrK : frontier K ⊆ K := hK.isClosed.frontier_subset
  have hAK' : A ⊆ K := hAK.trans hfrK
  have hintfr : ∀ z ∈ interior K, z ∉ frontier K := fun z hz h => h.2 hz
  have hXint : ∀ z ∈ interior K, z ∉ X := fun z hz hzX =>
    hintfr z hz (hAK (hXK ⟨hzX, interior_subset hz⟩).1)
  -- Step 1: `A ∪ B` separates `a` from `a'`
  have h1 : a' ∉ connectedComponentIn (A ∪ B)ᶜ a := by
    intro h
    have hsub : connectedComponentIn (A ∪ B)ᶜ a ⊆ Kᶜ := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
        hK.isClosed.isOpen_compl isOpen_interior
        (disjoint_compl_left.mono_right interior_subset) (fun z hz => ?_)
        ⟨a, mem_connectedComponentIn fun h => ha ((h.elim (fun h => hAK' h)
          fun h => (hBK.trans hfrK) h)), ha⟩
      by_cases hzK : z ∈ K
      · right
        by_contra hzi
        exact (connectedComponentIn_subset _ _ hz) (hfr ⟨subset_closure hzK, hzi⟩)
      · exact Or.inl hzK
    exact (hsub h) (interior_subset ha')
  -- Step 2: `X ∪ A` separates `a` from `a'`
  have h2 : a' ∉ connectedComponentIn (X ∪ A)ᶜ a :=
    sep_glue hX hXc hA hB hAB h1 (mem_cc_of_segment haa')
      (fun h => ha (hAK' h)) (fun h => hintfr a' ha' (hAK h))
  -- Step 3: `b ~ a'` off `X ∪ A`
  have hintsub : interior K ⊆ (X ∪ A)ᶜ := fun z hz h =>
    h.elim (hXint z hz) fun h => hintfr z hz (hAK h)
  have h3 : a' ∈ connectedComponentIn (X ∪ A)ᶜ b := by
    have hb'a' : a' ∈ connectedComponentIn (X ∪ A)ᶜ b' :=
      hint.subset_connectedComponentIn hb' hintsub ha'
    rw [connectedComponentIn_eq (mem_cc_of_segment hbb')]; exact hb'a'
  have hsepab : b ∉ connectedComponentIn (X ∪ A)ᶜ a := by
    intro h
    rw [connectedComponentIn_eq h] at h2
    exact h2 h3
  -- Step 4: glue with `K`
  have hKab : b ∈ connectedComponentIn (K ∪ A)ᶜ a := by
    rw [union_eq_left.2 hAK']
    exact hKo.subset_connectedComponentIn ha subset_rfl hb
  exact sep_glue hK hKc hX hA (inter_subset_right.trans hAK') hsepab hKab
    (fun h => haa' (left_mem_segment ℝ a a') (Or.inl h))
    (fun h => hbb' (left_mem_segment ℝ b b') (Or.inl h))

/-- Of two components of the complement of a compact set, at least one is bounded. -/
theorem bounded_of_sep {S : Set ℂ} (hS : IsCompact S) {a b : ℂ}
    (hab : b ∉ connectedComponentIn Sᶜ a) :
    Bornology.IsBounded (connectedComponentIn Sᶜ a) ∨
      Bornology.IsBounded (connectedComponentIn Sᶜ b) := by
  by_contra h
  push Not at h
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball (0 : ℂ)
  have hR0 : 0 ≤ R := by
    by_contra hneg
    push Not at hneg
    have : S = ∅ := by
      ext z; simp only [mem_empty_iff_false, iff_false]
      intro hz; have := hR hz; rw [mem_ball_zero_iff] at this; linarith [norm_nonneg z]
    subst this
    exact hab (by simpa using
      (isPreconnected_univ.subset_connectedComponentIn (mem_univ a) (by simp) (mem_univ b)))
  set w : ℂ := ((R + 1 : ℝ) : ℂ)
  have hw : R < ‖w‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hdis : ∀ x, Disjoint (connectedComponentIn Sᶜ x) S := fun x =>
    Set.disjoint_left.2 fun z hz hzS => connectedComponentIn_subset _ _ hz hzS
  have ha := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
    isPreconnected_connectedComponentIn h.1 (hdis a) hw
  have hb := QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR
    isPreconnected_connectedComponentIn h.2 (hdis b) hw
  have haS : a ∈ Sᶜ := by
    by_contra haS
    exact h.1 (by rw [connectedComponentIn_eq_empty haS]; exact Bornology.isBounded_empty)
  have hbS : b ∈ Sᶜ := by
    by_contra hbS
    exact h.2 (by rw [connectedComponentIn_eq_empty hbS]; exact Bornology.isBounded_empty)
  have h1 := ha (mem_connectedComponentIn haS)
  have h2 := hb (mem_connectedComponentIn hbS)
  exact hab (by rw [← connectedComponentIn_eq h1]; exact h2)

/-- **GM L4.13 crosscut fact** (tex l. 2081): in the setting of `theta_sep`, the components of
`(K ∪ X)ᶜ` at `a` and at `b` are distinct and at least one of them is bounded. -/
theorem theta_bounded {K X A B : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) (hint : IsPreconnected (interior K)) (hX : IsCompact X)
    (hXc : IsConnected X) (hA : IsCompact A) (hB : IsCompact B) (hAK : A ⊆ frontier K)
    (hBK : B ⊆ frontier K) (hfr : frontier K ⊆ A ∪ B) (hXK : X ∩ K ⊆ A ∩ B) (hAB : A ∩ B ⊆ X)
    {a b a' b' : ℂ} (ha : a ∉ K) (hb : b ∉ K) (ha' : a' ∈ interior K) (hb' : b' ∈ interior K)
    (haa' : segment ℝ a a' ⊆ (X ∪ B)ᶜ) (hbb' : segment ℝ b b' ⊆ (X ∪ A)ᶜ) :
    b ∉ connectedComponentIn (K ∪ X)ᶜ a ∧
      (Bornology.IsBounded (connectedComponentIn (K ∪ X)ᶜ a) ∨
        Bornology.IsBounded (connectedComponentIn (K ∪ X)ᶜ b)) := by
  have h := theta_sep hK hKc hKo hint hX hXc hA hB hAK hBK hfr hXK hAB ha hb ha' hb' haa' hbb'
  exact ⟨h, bounded_of_sep (hK.union hX) h⟩

end LQGMetric.Topo.Crosscut
