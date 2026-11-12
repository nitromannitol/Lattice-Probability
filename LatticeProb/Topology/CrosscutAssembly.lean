import LatticeProb.Topology.CrosscutArc
import LatticeProb.Topology.CrosscutSides
import LatticeProb.Topology.CrosscutLoop
import LatticeProb.Topology.NonCutContinuum
import LatticeProb.Topology.PolygonalCrossingData
import LatticeProb.Topology.TorhorstAssembly

/-!
# Separation of the frontier by a locally polygonal crosscut

The crosscut step in the proof of Torhorst's theorem (Torhorst (1921); Whyburn, *Analytic Topology*, Chapter VI;
Kuratowski, *Topology* II, §61). Let `K ⊆ ℂ` be a locally connected continuum without cut points, `C` a
complementary domain of `K` and `a ≠ b` two points of `frontier C`. A *crosscut* of `C` from `a` to `b` is an arc
`γ = f([0,1])` with `f 0 = a`, `f 1 = b` and `f((0,1)) ⊆ C`. We call it *locally two-sided* when every interior point
`y` of `γ` has a ball `B(y, r) ⊆ C` with `B(y, r) \ γ` the union of two preconnected sets whose closures both contain
`γ ∩ B(y, r)`, and we ask that `γ` agree with a straight segment on some ball around one interior point.

* `not_isPreconnected_frontier_diff_pair_of_locallyPolygonal_crosscut`: such a crosscut separates `frontier C`
  between `a` and `b`, i.e. `frontier C \ {a, b}` is not preconnected.
* `torhorstSimpleLoop_of_locallyPolygonal_crosscuts`: if any two frontier points of a complementary domain are
  joined by such a crosscut, then Torhorst's theorem `TorhorstSimpleLoop` holds.

The proof combines the components of `C \ γ` near the straight piece (each component has the whole of `γ` in its
closure, so it is one of the two components on the two sides of the straight piece), the loop obstruction for a
frontier point in the closures of both sides (through a subcontinuum of `K` joining `a` to `b` and missing that
point, which exists since `K` has no cut points), and the set-topological separation of the frontier by a crosscut.
-/

open Set Metric ComplexConjugate
open scoped Topology

namespace LatticeProb.Topology

/-- **A locally two-sided crosscut with a straight piece separates the frontier.** Let `K ⊆ ℂ` be a compact,
connected, nontrivial, locally connected set without cut points, `C` a connected component of `ℂ \ K` and
`a, b ∈ frontier C`. Let `γ = f([0,1])` be an arc from `a` to `b` whose interior `f((0,1))` lies in `C`, such that
at every interior point `y` some ball `B(y, r) ⊆ C` is cut by `γ` into two preconnected pieces whose closures both
contain `γ ∩ B(y, r)`, and such that on some ball `B(f t₀, r) ⊆ C` the arc agrees with a segment `[c, d]` through
`f t₀` of half-lengths at least `r`. Then `frontier C \ {a, b}` is not preconnected. -/
theorem not_isPreconnected_frontier_diff_pair_of_locallyPolygonal_crosscut {K C : Set ℂ} {a b : ℂ}
    (hK : IsCompact K) (hKc : IsConnected K) (hKn : K.Nontrivial) (hKlc : IsLocallyConnectedSet K)
    (hcut : ∀ x : ℂ, ¬ IsCutPoint K x) (hC : C ∈ connectedComponentsIn Kᶜ)
    (ha : a ∈ frontier C) (hb : b ∈ frontier C)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) (hfi : InjOn f (Icc 0 1)) (hf0 : f 0 = a) (hf1 : f 1 = b)
    (hγC : f '' Ioo 0 1 ⊆ C)
    (hloc : ∀ y ∈ f '' Ioo 0 1, ∃ r > 0, ball y r ⊆ C ∧ ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧
      IsPreconnected P₂ ∧ ball y r \ f '' Icc 0 1 = P₁ ∪ P₂ ∧
      f '' Icc 0 1 ∩ ball y r ⊆ closure P₁ ∩ closure P₂)
    {t₀ r : ℝ} {c d : ℂ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) (hcd : f t₀ ∈ openSegment ℝ c d)
    (hrc : r ≤ ‖c - f t₀‖) (hrd : r ≤ ‖d - f t₀‖) (hrC : ball (f t₀) r ⊆ C)
    (hseg : f '' Icc 0 1 ∩ ball (f t₀) r = segment ℝ c d ∩ ball (f t₀) r) :
    ¬ IsPreconnected (frontier C \ {a, b}) := by
  subst hf0 hf1
  have hKcl : IsClosed K := hK.isClosed
  have hCo : IsOpen C := isOpen_of_mem_connectedComponentsIn_compl hKcl hC
  have hCK : Disjoint C K := subset_compl_iff_disjoint_right.1 (subset_of_mem_connectedComponentsIn hC)
  have hFK : frontier C ⊆ K := frontier_subset_of_mem_connectedComponentsIn_compl hKcl hC
  have hCc : IsPreconnected C := (isConnected_of_mem_connectedComponentsIn hC).isPreconnected
  have haK : f 0 ∈ K := hFK ha
  have hbK : f 1 ∈ K := hFK hb
  have h0 : f 0 ∉ C := fun h => hCK.ne_of_mem h haK rfl
  have h1 : f 1 ∉ C := fun h => hCK.ne_of_mem h hbK rfl
  have hγ0 : f 0 ∈ f '' Icc 0 1 := ⟨0, left_mem_Icc.2 zero_le_one, rfl⟩
  have hγ1 : f 1 ∈ f '' Icc 0 1 := ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩
  have hγK : f '' Icc 0 1 ∩ K ⊆ {f 0, f 1} := by
    rintro y ⟨⟨t, ht, rfl⟩, hyK⟩
    obtain rfl | ht0 := ht.1.eq_or_lt
    · exact Or.inl rfl
    obtain rfl | ht1 := ht.2.eq_or_lt
    · exact Or.inr rfl
    exact (hCK.ne_of_mem (hγC ⟨t, ⟨ht0, ht1⟩, rfl⟩) hyK rfl).elim
  have hO : IsOpen (C \ f '' Icc 0 1) := hCo.sdiff (isCompact_Icc.image_of_continuousOn hf).isClosed
  obtain ⟨P₁, P₂, p, q, c', d', hP₁, hP₂, hsplit, -, hqP, hpP, hpqB, hepq, hpqγ, hecd, hcdγ, htrans⟩ :=
    exists_crossing_data_of_inter_ball_eq_segment hcd hr hrc hrd hseg
  have hPO : P₁ ∪ P₂ ⊆ C \ f '' Icc 0 1 := by
    rw [← hsplit]
    exact fun z hz => ⟨hrC hz.1, hz.2⟩
  have hBO : ball (f t₀) r ∩ (C \ f '' Icc 0 1) ⊆ P₁ ∪ P₂ := by
    rw [← hsplit]
    exact fun z hz => ⟨hz.1, hz.2.2⟩
  have hqO : q ∈ C \ f '' Icc 0 1 := hPO (Or.inl hqP)
  have hpO : p ∈ C \ f '' Icc 0 1 := hPO (Or.inr hpP)
  have hsep : ¬ IsPreconnected (C \ f '' Icc 0 1) :=
    not_isPreconnected_diff_arc_of_transverse hCo hKc.isPreconnected hCK hf hfi haK hbK ht₀ (hpqB.trans hrC)
      hepq hpqγ hecd hcdγ htrans
  -- every component of `C \ γ` is the component of `q` or the component of `p`
  have hcomp : ∀ U ∈ connectedComponentsIn (C \ f '' Icc 0 1),
      U = connectedComponentIn (C \ f '' Icc 0 1) q ∨ U = connectedComponentIn (C \ f '' Icc 0 1) p :=
    fun U hU => eq_or_eq_of_mem_closure_of_mem_connectedComponentsIn hU
      (mem_closure_of_mem_connectedComponentsIn_diff_arc hCo hCc hf hγC h0 h1 hloc hU ⟨t₀, ht₀, rfl⟩)
      (ball_mem_nhds _ hr) hP₁ hP₂ hPO hBO hqP hpP
  -- no frontier point off `γ` lies in the closures of both sides
  have hkey₀ : ∀ x ∈ frontier C \ f '' Icc 0 1, x ∉ closure (connectedComponentIn (C \ f '' Icc 0 1) q) ∩
      closure (connectedComponentIn (C \ f '' Icc 0 1) p) := by
    rintro x ⟨-, hxγ⟩
    have hax : f 0 ∉ ({x} : Set ℂ) := fun h => hxγ ((mem_singleton_iff.1 h) ▸ hγ0)
    have hbx : f 1 ∉ ({x} : Set ℂ) := fun h => hxγ ((mem_singleton_iff.1 h) ▸ hγ1)
    obtain ⟨H, hHc, hHp, hHK, haH, hbH⟩ :=
      exists_isCompact_isPreconnected_of_not_isCutPoint hK hKc hKlc (hcut x) ⟨haK, hax⟩ ⟨hbK, hbx⟩
    exact not_mem_closure_inter_closure_of_transverse hHp hHc.isClosed (hCK.mono_right (hHK.trans sdiff_subset))
      hf hfi haH hbH ht₀ (hpqB.trans hrC) hepq hpqγ hecd hcdγ htrans hO.connectedComponentIn
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) (mem_connectedComponentIn hqO)
      hO.connectedComponentIn isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn hpO) fun h => h.elim (fun hxH => (hHK hxH).2 (mem_singleton x)) hxγ
  have hkey : ∀ x ∈ frontier C \ f '' Icc 0 1, ∀ U ∈ connectedComponentsIn (C \ f '' Icc 0 1),
      ∀ V ∈ connectedComponentsIn (C \ f '' Icc 0 1), x ∈ closure U → x ∈ closure V → U = V := by
    intro x hx U hU V hV hxU hxV
    rcases hcomp U hU with rfl | rfl <;> rcases hcomp V hV with rfl | rfl
    · rfl
    · exact (hkey₀ x hx ⟨hxU, hxV⟩).elim
    · exact (hkey₀ x hx ⟨hxV, hxU⟩).elim
    · rfl
  have hfin : ∀ x ∈ frontier C \ f '' Icc 0 1, ∃ N ∈ 𝓝 x,
      {U ∈ connectedComponentsIn (C \ f '' Icc 0 1) | (U ∩ N).Nonempty}.Finite := fun _ _ =>
    ⟨univ, Filter.univ_mem,
      (finite_connectedComponentsIn_diff_arc hCo hCc hf hγC h0 h1 hloc).subset fun _ hU => hU.1⟩
  exact not_isPreconnected_frontier_diff_pair_of_crosscut hKcl hKc.isPreconnected hKn hC ⟨f, hf, hfi, rfl⟩
    hγ0 hγ1 hγK hsep hkey hfin

/-- **Torhorst's theorem from locally polygonal crosscuts.** If any two distinct frontier points `a, b` of a
complementary domain `C` of a locally connected plane continuum `K` without cut points are joined by a crosscut of
`C` that is locally two-sided at its interior points and straight near one of them, then the frontier of every
complementary domain of a nondegenerate locally connected plane continuum without cut points is a simple closed
curve. -/
theorem torhorstSimpleLoop_of_locallyPolygonal_crosscuts
    (hCross : ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
      (∀ x : ℂ, ¬ IsCutPoint K x) → ∀ C ∈ connectedComponentsIn Kᶜ, ∀ a ∈ frontier C, ∀ b ∈ frontier C,
      a ≠ b → ∃ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f 0 = a ∧ f 1 = b ∧
        f '' Ioo 0 1 ⊆ C ∧
        (∀ y ∈ f '' Ioo 0 1, ∃ r > 0, ball y r ⊆ C ∧ ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧
          IsPreconnected P₂ ∧ ball y r \ f '' Icc 0 1 = P₁ ∪ P₂ ∧
          f '' Icc 0 1 ∩ ball y r ⊆ closure P₁ ∩ closure P₂) ∧
        ∃ t₀ ∈ Ioo (0 : ℝ) 1, ∃ r > 0, ∃ c d : ℂ, f t₀ ∈ openSegment ℝ c d ∧ r ≤ ‖c - f t₀‖ ∧
          r ≤ ‖d - f t₀‖ ∧ ball (f t₀) r ⊆ C ∧
          f '' Icc 0 1 ∩ ball (f t₀) r = segment ℝ c d ∩ ball (f t₀) r) :
    TorhorstSimpleLoop :=
  torhorstSimpleLoop_of_pairSeparates fun K hK hKc hKn hKlc hcut C hC a ha b hb hab => by
    obtain ⟨f, hf, hfi, hf0, hf1, hγC, hloc, t₀, ht₀, r, hr, c, d, hcd, hrc, hrd, hrC, hseg⟩ :=
      hCross K hK hKc hKn hKlc hcut C hC a ha b hb hab
    exact not_isPreconnected_frontier_diff_pair_of_locallyPolygonal_crosscut hK hKc hKn hKlc hcut hC ha hb hf hfi
      hf0 hf1 hγC hloc ht₀ hr hcd hrc hrd hrC hseg

end LatticeProb.Topology
