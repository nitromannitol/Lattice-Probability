/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.CrosscutSep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutRadial
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.JordanChord

/-!
# Crosscuts by circle arcs, part II: the two sides of the arc are separated

`Y` a component of `sphere c r ∖ K` (`K` compact connected). `cc_sep`: a point `a` inside and a
point `b` outside the circle that are not separated by `K ∪ (sphere c r ∖ Y)` are separated by
`Y ∪ K`.

**Proof (Eilenberg's criterion and gluing of logarithms, as in the proof of Janiszewski's theorem,
R. B. Burckel, *Classical Analysis in the Complex Plane* (2021), Ex. 4.37(i)–(ii), printed p. 215;
QuantumZipper `CA.Topo.janiszewski`).** With `f z = (z - a)/(z - b)`, if `Y ∪ K` did not separate
`a, b`, `f` would have continuous logarithms `L₂` on `Y ∪ K` and `L₁` on `K ∪ A`
(`A = sphere c r ∖ Y`). On the connected set `K`, `L₂ - L₁` is a constant `c₀ ∈ 2πiℤ`; since
`closure Y ∖ Y ⊆ K`, pasting `L₂` on `closure Y` with `L₁ + c₀` on `A` gives a continuous logarithm
of `f` on the circle, so the circle would not separate `a` from `b`: contradiction.
This is the separation half of Pommerenke, *Boundary Behaviour of Conformal Maps*, Prop. 2.12, by
an own elementary route (no conformal maps), recorded in `DEVIATIONS.md` (proposed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter Complex
open QuantumZipper.CA.Topo

namespace LQGMetric.Topo.Crosscut

theorem cc_subset_sphere (K : Set ℂ) (c y₀ : ℂ) (r : ℝ) :
    connectedComponentIn (sphere c r \ K) y₀ ⊆ sphere c r :=
  (connectedComponentIn_subset _ _).trans sdiff_subset

/-- The closure of a component of `sphere c r ∖ K` adds only points of `K`. -/
theorem closure_cc_sub (K : Set ℂ) (c y₀ : ℂ) (r : ℝ) :
    closure (connectedComponentIn (sphere c r \ K) y₀) ⊆
      connectedComponentIn (sphere c r \ K) y₀ ∪ K := by
  intro z hz
  by_cases hzK : z ∈ K
  · exact Or.inr hzK
  left
  have hzS : z ∈ sphere c r := (isClosed_sphere.closure_subset_iff.2 (cc_subset_sphere K c y₀ r)) hz
  rcases (connectedComponentIn (sphere c r \ K) y₀).eq_empty_or_nonempty with hY | hYne
  · rw [hY, closure_empty] at hz; exact hz.elim
  have hy₀ : y₀ ∈ sphere c r \ K := connectedComponentIn_nonempty_iff.1 hYne
  have hT : IsPreconnected (insert z (connectedComponentIn (sphere c r \ K) y₀)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hz subset_closure)
  exact hT.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hy₀))
    (insert_subset (show z ∈ sphere c r \ K from ⟨hzS, hzK⟩) (connectedComponentIn_subset _ _)) (mem_insert _ _)

theorem isClosed_cc_union (K : Set ℂ) (hK : IsClosed K) (c y₀ : ℂ) (r : ℝ) :
    IsClosed (connectedComponentIn (sphere c r \ K) y₀ ∪ K) := by
  refine isClosed_of_closure_subset ?_
  rw [closure_union, hK.closure_eq]
  exact union_subset (closure_cc_sub K c y₀ r) subset_union_right

theorem isCompact_cc_union {K : Set ℂ} (hK : IsCompact K) (c y₀ : ℂ) (r : ℝ) :
    IsCompact (connectedComponentIn (sphere c r \ K) y₀ ∪ K) :=
  isCompact_of_isClosed_isBounded (isClosed_cc_union K hK.isClosed c y₀ r)
    ((isBounded_sphere.subset (cc_subset_sphere K c y₀ r)).union hK.isBounded)

/-- The rest of the circle, `sphere c r ∖ Y`, is closed. -/
theorem isClosed_sphere_diff_cc {K : Set ℂ} (hK : IsClosed K) (hKne : K.Nonempty) {c : ℂ}
    (y₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    IsClosed (sphere c r \ connectedComponentIn (sphere c r \ K) y₀) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzS : z ∈ sphere c r := isClosed_sphere.closure_subset_iff.2 sdiff_subset hz
  refine ⟨hzS, fun hzY => ?_⟩
  have hzK : z ∉ K := ((connectedComponentIn_subset _ _) hzY).2
  obtain ⟨ρ, hρ, hball⟩ := cc_sphere_open hK hKne hr hzS hzK
  rw [← connectedComponentIn_eq hzY] at hball
  obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.1 hz ρ hρ
  exact hw.2 (hball ⟨by rw [mem_ball, dist_comm]; exact hwz, hw.1⟩)

/-- The component of the complement of the circle at an inside point lies in the open disc. -/
theorem cc_compl_sphere_subset {c a : ℂ} {r : ℝ} (ha : ‖a - c‖ < r) :
    connectedComponentIn (sphere c r)ᶜ a ⊆ ball c r := by
  have haS : a ∈ (sphere c r)ᶜ := fun h => by
    rw [mem_sphere, dist_eq_norm] at h; linarith
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_ball
    isClosed_closedBall.isOpen_compl (disjoint_compl_right.mono_left ball_subset_closedBall)
    (fun z hz => ?_) ⟨a, mem_connectedComponentIn haS, by rwa [mem_ball, dist_eq_norm]⟩
  have hz' : dist z c ≠ r := fun h => (connectedComponentIn_subset _ _ hz) h
  rcases lt_or_gt_of_ne hz' with h | h
  · exact Or.inl h
  · exact Or.inr (fun h' => absurd (mem_closedBall.1 h') (not_le.2 h))

/-- **Separation by the arc.** -/
theorem cc_sep {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) {c : ℂ} (y₀ : ℂ) {r : ℝ}
    (hr : 0 < r) {a b : ℂ} (ha : ‖a - c‖ < r) (hb : r < ‖b - c‖)
    (hab : b ∈ connectedComponentIn
      (K ∪ (sphere c r \ connectedComponentIn (sphere c r \ K) y₀))ᶜ a) :
    b ∉ connectedComponentIn (connectedComponentIn (sphere c r \ K) y₀ ∪ K)ᶜ a := by
  intro hb'
  set Y := connectedComponentIn (sphere c r \ K) y₀ with hYdef
  set A := sphere c r \ Y
  have hKne := hKc.nonempty
  have hAcl : IsClosed A := isClosed_sphere_diff_cc hK.isClosed hKne y₀ hr
  have hAc : IsCompact A := (isCompact_sphere c r).of_isClosed_subset hAcl sdiff_subset
  obtain ⟨L1, hL1c, hL1⟩ := hasLogOn_of_not_separates (hK.union hAc) hab
  obtain ⟨L2, hL2c, hL2⟩ := hasLogOn_of_not_separates (isCompact_cc_union hK c y₀ r) hb'
  have haS : a ∉ sphere c r := fun h => by rw [mem_sphere, dist_eq_norm] at h; linarith
  have hbS : b ∉ sphere c r := fun h => by rw [mem_sphere, dist_eq_norm] at h; linarith
  have haK : a ∉ K := fun h => (connectedComponentIn_nonempty_iff.1 ⟨b, hab⟩) (Or.inl h)
  have hbK : b ∉ K := fun h => (connectedComponentIn_subset _ _ hab) (Or.inl h)
  have hconst : ∀ {u v : ℂ}, u ∈ K → v ∈ K → L2 u - L1 u = L2 v - L1 v := fun hu hv =>
    QuantumZipper.JordanChord.log_sub_eq_of_isPreconnected hKc.isPreconnected
      (hL2c.mono subset_union_right) (hL1c.mono subset_union_left)
      (fun z hz => (hL2 z (Or.inr hz)).trans (hL1 z (Or.inl hz)).symm) hu hv
  obtain ⟨k₀, hk₀⟩ := hKne
  set c₀ := L2 k₀ - L1 k₀
  have hc₀ : ∀ z ∈ K, L2 z = L1 z + c₀ := fun z hz => by
    have := hconst hz hk₀; simp only [c₀]; linear_combination this
  have hexp : Complex.exp c₀ = 1 := by
    have h1 : Complex.exp (L2 k₀) = (k₀ - a) / (k₀ - b) := hL2 k₀ (Or.inr hk₀)
    have h2 : Complex.exp (L1 k₀) = (k₀ - a) / (k₀ - b) := hL1 k₀ (Or.inl hk₀)
    have hf0 : (k₀ - a) / (k₀ - b) ≠ 0 :=
      div_ne_zero (sub_ne_zero.2 fun h => haK (h ▸ hk₀)) (sub_ne_zero.2 fun h => hbK (h ▸ hk₀))
    simp only [c₀, Complex.exp_sub, h1, h2, div_self hf0]
  classical
  let L : ℂ → ℂ := fun z => if z ∈ Y then L2 z else L1 z + c₀
  have hS : sphere c r ⊆ closure Y ∪ A := fun z hz => by
    by_cases h : z ∈ Y
    · exact Or.inl (subset_closure h)
    · exact Or.inr ⟨hz, h⟩
  have hclY : closure Y ⊆ Y ∪ K := closure_cc_sub K c y₀ r
  have hLc : ContinuousOn L (closure Y ∪ A) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_closure hAcl
    · refine (hL2c.mono hclY).congr fun z hz => ?_
      by_cases h : z ∈ Y
      · simp [L, h]
      · simp only [L, h, ite_false]; exact (hc₀ z ((hclY hz).resolve_left h)).symm
    · refine ((hL1c.mono subset_union_right).add (continuousOn_const (c := c₀))).congr fun z hz => ?_
      simp [L, hz.2]
  have hlog : HasLogOn (fun z => (z - a) / (z - b)) (sphere c r) := by
    refine ⟨L, hLc.mono hS, fun z hz => ?_⟩
    by_cases h : z ∈ Y
    · simp only [L, h, ite_true]; exact hL2 z (Or.inl h)
    · simp only [L, h, ite_false]; rw [Complex.exp_add, hexp, mul_one]; exact hL1 z (Or.inr ⟨hz, h⟩)
  have h := cc_compl_sphere_subset ha (not_separates_of_hasLogOn (isCompact_sphere c r) haS hbS hlog)
  rw [mem_ball, dist_eq_norm] at h; linarith

end LQGMetric.Topo.Crosscut
