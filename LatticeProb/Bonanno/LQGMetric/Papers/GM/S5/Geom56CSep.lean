/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CSep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Defs

/-!
# GM Lemma 5.6, condition (2): the abstract corridor separation lemma (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6, condition (2) (l. 2982–2989), with the axis-parallel corridor of decision D69 and the
disconnection clause of decision D77.

GM's argument: the squares of the `z − 2r` side (`π₋ ∪ L₋`) that come near the rest of the tube lie
in `O_u`, and outside `O_u` the two sides are at distance `≥ ε₁ r`. `sepDisc_of_corridor` is this
argument for a general open set `V ⊆ K_a ∪ K_r` (`K_a` the `a`-side, `K_r` the rest):

* near `u'`, `K_a` lies in the closure of an open convex corridor `R ⊆ V` containing `u'`; then
  `cl R ∩ B_ρ(u') ∩ V ⊆ O_{u'}` (segments to `u'`);
* outside `B_ρ(u')`, `K_a` is at distance `≥ d` from `K_r`;
* `(V ∩ K_a) ∖ B_ρ(u')` is preconnected and contains `a`; `b ∉ K_a`.

Then the component of `a` in `V ∖ O_{u'}` is exactly `(V ∩ K_a) ∖ B_ρ(u')`, it is `d`-separated
from the rest, and `b` is not in it. Own elementary argument (GM leave these steps implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology

namespace LQGMetric.GM
open Blueprint

/-- a `d`-separated piece `P ∋ a` of `S` contains the component of `a` in `S` (copy of
`connectedComponentIn_subset_of_sep`, Geom58Sep.lean by P2-M2L58, kept here so that this module
does not depend on the L5.8 files) -/
lemma compIn_subset_of_sep56 {S P : Set ℂ} {a : ℂ} {d : ℝ} (hd : 0 < d) (ha : a ∈ P)
    (hsep : ∀ p ∈ P, ∀ q ∈ S, q ∉ P → d ≤ dist p q) : connectedComponentIn S a ⊆ P := by
  by_cases haS : a ∈ S
  swap
  · rw [connectedComponentIn_eq_empty haS]; exact empty_subset _
  set K := connectedComponentIn S a
  have hK : IsPreconnected K := isPreconnected_connectedComponentIn
  have hdisj : Disjoint (thickening (d / 2) P) (thickening (d / 2) (S \ P)) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    obtain ⟨p, hp, hwp⟩ := mem_thickening_iff.1 hw1
    obtain ⟨q, ⟨hqS, hqP⟩, hwq⟩ := mem_thickening_iff.1 hw2
    have := hsep p hp q hqS hqP
    have := dist_triangle_left p q w
    linarith
  have hcov : K ⊆ thickening (d / 2) P ∪ thickening (d / 2) (S \ P) := by
    intro w hw
    by_cases hwP : w ∈ P
    · exact Or.inl (self_subset_thickening (by linarith) _ hwP)
    · exact Or.inr (self_subset_thickening (by linarith) _ ⟨connectedComponentIn_subset _ _ hw, hwP⟩)
  rcases hK.subset_or_subset isOpen_thickening isOpen_thickening hdisj hcov with h | h
  · intro w hw
    by_contra hwP
    obtain ⟨p, hp, hwp⟩ := mem_thickening_iff.1 (h hw)
    have := hsep p hp w (connectedComponentIn_subset _ _ hw) hwP
    rw [dist_comm] at hwp; linarith
  · exfalso
    obtain ⟨q, ⟨hqS, hqP⟩, haq⟩ := mem_thickening_iff.1 (h (mem_connectedComponentIn haS))
    have := hsep a ha q hqS hqP
    linarith

/-- points of the closed corridor near `u'` that lie in `V` are in `O_{u'}` -/
lemma closure_corridor_subset_nearComp {V R : Set ℂ} {u' : ℂ} {ρ : ℝ} (hR : IsOpen R)
    (hRc : Convex ℝ R) (hRV : R ⊆ V) (hu' : u' ∈ R) :
    closure R ∩ ball u' ρ ∩ V ⊆ nearComp V ρ u' := by
  rintro p ⟨⟨hpR, hpB⟩, hpV⟩
  have hu'B : u' ∈ ball u' ρ := mem_ball_self (pos_of_mem_ball hpB)
  have hseg : segment ℝ u' p ⊆ V ∩ ball u' ρ := by
    intro w hw
    refine ⟨?_, (convex_ball u' ρ).segment_subset hu'B hpB hw⟩
    rw [← insert_endpoints_openSegment] at hw
    rcases hw with rfl | rfl | hw
    · exact hRV hu'
    · exact hpV
    · have := hRc.openSegment_interior_closure_subset_interior (hR.interior_eq.symm ▸ hu') hpR hw
      rw [hR.interior_eq] at this
      exact hRV this
  exact (convex_segment u' p).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ u' p) hseg (right_mem_segment ℝ u' p)

/-- **GM l. 2982–2989, abstract form**: see the module docstring -/
theorem sepDisc_of_corridor {V Ka Kr R : Set ℂ} {u' a b : ℂ} {ρ d : ℝ} (hd : 0 < d)
    (hVK : V ⊆ Ka ∪ Kr) (hR : IsOpen R) (hRc : Convex ℝ R) (hRV : R ⊆ V) (hu' : u' ∈ R)
    (hKaB : Ka ∩ ball u' ρ ⊆ closure R)
    (hfar : ∀ x ∈ Ka \ ball u' ρ, ∀ y ∈ Kr, d ≤ dist x y)
    (hconn : IsPreconnected ((V ∩ Ka) \ ball u' ρ))
    (ha : a ∈ (V ∩ Ka) \ ball u' ρ) (hb : b ∉ Ka) :
    SepFrom V (nearComp V ρ u') a d ∧ b ∉ connectedComponentIn (V \ nearComp V ρ u') a := by
  set O := nearComp V ρ u'
  set X₁ := (V ∩ Ka) \ ball u' ρ
  have hOB : O ⊆ ball u' ρ := (connectedComponentIn_subset _ _).trans inter_subset_right
  have hX₁ : X₁ ⊆ V \ O := fun p hp => ⟨hp.1.1, fun h => hp.2 (hOB h)⟩
  have hin : ∀ p ∈ V \ O, p ∈ Ka → p ∈ X₁ := by
    intro p hp hpK
    refine ⟨⟨hp.1, hpK⟩, fun hpB => hp.2 ?_⟩
    exact closure_corridor_subset_nearComp hR hRc hRV hu' ⟨⟨hKaB ⟨hpK, hpB⟩, hpB⟩, hp.1⟩
  have hsub1 : X₁ ⊆ connectedComponentIn (V \ O) a :=
    hconn.subset_connectedComponentIn ha hX₁
  have hsep : ∀ p ∈ X₁, ∀ q ∈ V \ O, q ∉ X₁ → d ≤ dist p q := by
    intro p hp q hq hqX
    have hqK : q ∉ Ka := fun h => hqX (hin q hq h)
    have hqr : q ∈ Kr := (hVK hq.1).resolve_left hqK
    exact hfar p ⟨hp.1.2, hp.2⟩ q hqr
  have hsub2 : connectedComponentIn (V \ O) a ⊆ X₁ :=
    compIn_subset_of_sep56 hd ha hsep
  refine ⟨?_, fun hbc => hb (hsub2 hbc).1.2⟩
  intro x hx y hy hyc
  exact hsep x (hsub2 hx) y hy (fun h => hyc (hsub1 h))

/-- the robust form (`SepDiscNear`, decisions D69/D77): the hypotheses of `sepDisc_of_corridor`
at every `u'` near `u` -/
theorem sepDiscNear_of_corridor {V Ka Kr : Set ℂ} {u a b : ℂ} {ρ d : ℝ} (hd : 0 < d)
    (hVK : V ⊆ Ka ∪ Kr) (hb : b ∉ Ka)
    (h : ∀ᶠ u' in 𝓝 u, ∃ R : Set ℂ, IsOpen R ∧ Convex ℝ R ∧ R ⊆ V ∧ u' ∈ R ∧
      Ka ∩ ball u' ρ ⊆ closure R ∧ (∀ x ∈ Ka \ ball u' ρ, ∀ y ∈ Kr, d ≤ dist x y) ∧
      IsPreconnected ((V ∩ Ka) \ ball u' ρ) ∧ a ∈ (V ∩ Ka) \ ball u' ρ) :
    SepDiscNear V ρ u a b d := by
  refine h.mono fun u' hu' => ?_
  obtain ⟨R, hR, hRc, hRV, hu'R, hKaB, hfar, hconn, ha⟩ := hu'
  exact sepDisc_of_corridor hd hVK hR hRc hRV hu'R hKaB hfar hconn ha hb

end LQGMetric.GM
