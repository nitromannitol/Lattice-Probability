/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Sep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes58Geom

/-!
# GM Lemma 5.8: the condition-2 transfer and (5.25), abstractly (task P2-M2L58)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 3, condition 2 (l. 3110–3126).

* `inter_ball_eq_of_closed`, `interior_closure_of_isSquareTube`: GM (5.25) (l. 3119) in the form
  "a closed set `B` disjoint from a ball does not change `interior (cl V ∪ B)` in that ball", and
  `interior (cl V) = V` for a square tube `V`.
* `sepFrom_transfer`: GM l. 3120–3126. If `U ∖ O = (V ∖ O) ∪ X ∪ Y`, where the `x`-side `X` is
  connected to `a = z − 2ρr` and the `y`-side `Y` to `b = z + 2ρr` inside `U ∖ O`, `X` and `Y` are
  `d`-separated, and every point of `V ∖ O` within distance `< d` of `X` (resp. `Y`) has its
  component of `V ∖ O` within distance `< d` of that of `a` (resp. `b`) ("the junction squares touch
  only the component of `z ∓ 2ρr`", decision D69), then condition 2 for `V` at `a` gives
  condition 2 for `U` at `x`. GM: "the connected component of `U ∖ O_u` which contains `x` is the
  union of `W_k(x)` and the connected component of `V ∖ O_u` which contains `z_k − 2ρr`". Here the
  component of `x` is `C ∪ X ∪ (Y if b ∈ C)`, `C` the component of `a` in `V ∖ O` (GM's text
  implicitly assumes `b ∉ C`; the case `b ∈ C` is handled the same way).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology

namespace LQGMetric.GM
open Blueprint

/-! ## (5.25): localisation of `interior (cl V ∪ B)` -/

lemma mem_interior_of_mem_interior_union {A B : Set ℂ} (hB : IsClosed B) {w : ℂ}
    (hw : w ∈ interior (A ∪ B)) (hwB : w ∉ B) : w ∈ interior A := by
  rw [mem_interior_iff_mem_nhds] at hw ⊢
  filter_upwards [hw, hB.isOpen_compl.mem_nhds hwB] with v h1 h2
  exact h1.resolve_right h2

lemma isClosed_gridSquare (s : ℝ) (m : ℤ × ℤ) : IsClosed (gridSquare s m) := by
  show IsClosed ({x : ℂ | (m.1 : ℝ) * s ≤ x.re} ∩ ({x : ℂ | x.re ≤ ((m.1 : ℝ) + 1) * s} ∩
    ({x : ℂ | (m.2 : ℝ) * s ≤ x.im} ∩ {x : ℂ | x.im ≤ ((m.2 : ℝ) + 1) * s})))
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

/-! ## The condition-2 transfer -/

/-- the components of `S` through `p` and `q` come within distance `< d` of each other -/
def CompNear (S : Set ℂ) (d : ℝ) (p q : ℂ) : Prop :=
  ∃ p₁ ∈ connectedComponentIn S p, ∃ q₁ ∈ connectedComponentIn S q, dist p₁ q₁ < d

lemma CompNear.mono {S T : Set ℂ} (h : S ⊆ T) {d : ℝ} {p q : ℂ} (hn : CompNear S d p q) :
    CompNear T d p q := by
  obtain ⟨p₁, hp₁, q₁, hq₁, hd⟩ := hn
  exact ⟨p₁, connectedComponentIn_mono _ h hp₁, q₁, connectedComponentIn_mono _ h hq₁, hd⟩

lemma CompNear.symm {S : Set ℂ} {d : ℝ} {p q : ℂ} (hn : CompNear S d p q) : CompNear S d q p := by
  obtain ⟨p₁, hp₁, q₁, hq₁, hd⟩ := hn
  exact ⟨q₁, hq₁, p₁, hp₁, by rwa [dist_comm]⟩

lemma CompNear.of_mem_right {S : Set ℂ} {d : ℝ} {p q a : ℂ} (hn : CompNear S d p q)
    (hq : q ∈ connectedComponentIn S a) : CompNear S d p a := by
  rwa [CompNear, connectedComponentIn_eq hq]

/-- `SepFrom` at `a`: a point whose component is `d`-near that of `a` lies in it -/
lemma mem_comp_of_compNear {V O : Set ℂ} {a q : ℂ} {d : ℝ} (hsep : SepFrom V O a d)
    (hq : q ∈ V \ O) (hn : CompNear (V \ O) d q a) : q ∈ connectedComponentIn (V \ O) a := by
  obtain ⟨q₁, hq₁, q₂, hq₂, hd⟩ := hn
  have h1 : q₁ ∈ connectedComponentIn (V \ O) a := by
    by_contra hc
    have := hsep q₂ hq₂ q₁ (connectedComponentIn_subset _ _ hq₁) hc
    rw [dist_comm] at this; linarith
  rw [connectedComponentIn_eq h1, ← connectedComponentIn_eq hq₁]
  exact mem_connectedComponentIn hq

/-- a `d`-separated piece `P ∋ a` of `S` contains the component of `a` in `S` -/
lemma connectedComponentIn_subset_of_sep {S P : Set ℂ} {a : ℂ} {d : ℝ} (hd : 0 < d) (ha : a ∈ P)
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

/-- the core of GM l. 3120–3126: the component of `x` in `U ∖ O` lies in
`C ∪ X ∪ (Y if b ∈ C)`, `C` the component of `a` in `V ∖ O`, and this piece is `d`-separated
from the rest of `U ∖ O` -/
theorem transfer_core {U V O X Y : Set ℂ} {a b x : ℂ} {d : ℝ} (hd : 0 < d)
    (hVU : V ⊆ U) (hUV : U ⊆ V ∪ X ∪ Y) (ha : a ∈ V \ O) (hb : b ∈ V \ O)
    (hx : x ∈ connectedComponentIn (U \ O) a)
    (hX : ∀ w ∈ U \ O, w ∈ X → w ∈ connectedComponentIn (U \ O) a)
    (hY : ∀ w ∈ U \ O, w ∈ Y → w ∈ connectedComponentIn (U \ O) b)
    (hXY : ∀ p ∈ X, ∀ q ∈ Y, d ≤ dist p q)
    (hAX : ∀ p ∈ X, ∀ q ∈ V \ O, dist p q < d → CompNear (V \ O) d q a)
    (hAY : ∀ p ∈ Y, ∀ q ∈ V \ O, dist p q < d → CompNear (V \ O) d q b)
    (hsep : SepFrom V O a d) :
    let P : Set ℂ := connectedComponentIn (V \ O) a ∪ ((U \ O) ∩ X) ∪
      {w | b ∈ connectedComponentIn (V \ O) a ∧ w ∈ (U \ O) ∩ Y}
    connectedComponentIn (U \ O) x ⊆ P ∧ ∀ p ∈ P, ∀ q ∈ U \ O, q ∉ P → d ≤ dist p q := by
  set C := connectedComponentIn (V \ O) a
  let P : Set ℂ := C ∪ ((U \ O) ∩ X) ∪ {w | b ∈ C ∧ w ∈ (U \ O) ∩ Y}
  have hsepP : ∀ p ∈ P, ∀ q ∈ U \ O, q ∉ P → d ≤ dist p q := by
    intro p hp q hq hqP
    by_contra hlt
    push Not at hlt
    have hqC : q ∉ C := fun h => hqP (Or.inl (Or.inl h))
    have hqX : q ∉ X := fun h => hqP (Or.inl (Or.inr ⟨hq, h⟩))
    rcases hUV hq.1 with (hqV | hqX') | hqY
    · have hqVO : q ∈ V \ O := ⟨hqV, hq.2⟩
      rcases hp with (hpC | ⟨-, hpX⟩) | ⟨hbC, -, hpY⟩
      · exact absurd (hsep p hpC q hqVO hqC) (not_le.2 hlt)
      · exact hqC (mem_comp_of_compNear hsep hqVO (hAX p hpX q hqVO hlt))
      · exact hqC (mem_comp_of_compNear hsep hqVO ((hAY p hpY q hqVO hlt).of_mem_right hbC))
    · exact hqX hqX'
    · have hbC : b ∉ C := fun h => hqP (Or.inr ⟨h, hq, hqY⟩)
      rcases hp with (hpC | ⟨-, hpX⟩) | ⟨hbC', -, -⟩
      · have hpVO : p ∈ V \ O := connectedComponentIn_subset _ _ hpC
        have hn := hAY q hqY p hpVO (by rwa [dist_comm])
        exact hbC (mem_comp_of_compNear hsep hb (hn.symm.of_mem_right hpC))
      · exact absurd (hXY p hpX q hqY) (not_le.2 hlt)
      · exact hbC hbC'
  have haP : a ∈ P := Or.inl (Or.inl (mem_connectedComponentIn ha))
  have hKP := connectedComponentIn_subset_of_sep hd haP hsepP
  show connectedComponentIn (U \ O) x ⊆ P ∧ ∀ p ∈ P, ∀ q ∈ U \ O, q ∉ P → d ≤ dist p q
  refine ⟨?_, hsepP⟩
  rw [← connectedComponentIn_eq hx]
  exact hKP

/-- **GM l. 3120–3126**: the transfer of condition 2 from `V = V_{ρr}(z_k)` (at `a = z_k − 2ρr`)
to `U = U_r^{x,y}` (at `x`); see the module docstring -/
theorem sepFrom_transfer {U V O X Y : Set ℂ} {a b x : ℂ} {d : ℝ} (hd : 0 < d)
    (hVU : V ⊆ U) (hUV : U ⊆ V ∪ X ∪ Y) (ha : a ∈ V \ O) (hb : b ∈ V \ O)
    (hx : x ∈ connectedComponentIn (U \ O) a)
    (hX : ∀ w ∈ U \ O, w ∈ X → w ∈ connectedComponentIn (U \ O) a)
    (hY : ∀ w ∈ U \ O, w ∈ Y → w ∈ connectedComponentIn (U \ O) b)
    (hXY : ∀ p ∈ X, ∀ q ∈ Y, d ≤ dist p q)
    (hAX : ∀ p ∈ X, ∀ q ∈ V \ O, dist p q < d → CompNear (V \ O) d q a)
    (hAY : ∀ p ∈ Y, ∀ q ∈ V \ O, dist p q < d → CompNear (V \ O) d q b)
    (hsep : SepFrom V O a d) : SepFrom U O x d := by
  obtain ⟨hKP, hsepP⟩ := transfer_core hd hVU hUV ha hb hx hX hY hXY hAX hAY hsep
  have hPsub : connectedComponentIn (V \ O) a ∪ ((U \ O) ∩ X) ∪
      {w | b ∈ connectedComponentIn (V \ O) a ∧ w ∈ (U \ O) ∩ Y} ⊆ connectedComponentIn (U \ O) x := by
    rw [← connectedComponentIn_eq hx]
    rintro w ((hw | ⟨hwU, hwX⟩) | ⟨hbC, hwU, hwY⟩)
    · exact connectedComponentIn_mono _ (sdiff_subset_sdiff_left hVU) hw
    · exact hX w hwU hwX
    · rw [connectedComponentIn_eq (connectedComponentIn_mono _ (sdiff_subset_sdiff_left hVU) hbC)]
      exact hY w hwU hwY
  intro p hp q hq hqx
  exact hsepP p (hKP hp) q hq (fun h => hqx (hPsub h))

/-- **GM l. 3120–3124, the disconnection (decision D77)**: if `b = z_k + 2ρr` is not in the
component of `a = z_k − 2ρr` in `V ∖ O`, then a point `y ∈ Y` (GM's `W_k(y)`) of `U ∖ O` is not in
the component of `x` in `U ∖ O` -/
theorem discFrom_transfer {U V O X Y : Set ℂ} {a b x y : ℂ} {d : ℝ} (hd : 0 < d)
    (hVU : V ⊆ U) (hUV : U ⊆ V ∪ X ∪ Y) (ha : a ∈ V \ O) (hb : b ∈ V \ O)
    (hx : x ∈ connectedComponentIn (U \ O) a)
    (hX : ∀ w ∈ U \ O, w ∈ X → w ∈ connectedComponentIn (U \ O) a)
    (hY : ∀ w ∈ U \ O, w ∈ Y → w ∈ connectedComponentIn (U \ O) b)
    (hXY : ∀ p ∈ X, ∀ q ∈ Y, d ≤ dist p q)
    (hAX : ∀ p ∈ X, ∀ q ∈ V \ O, dist p q < d → CompNear (V \ O) d q a)
    (hAY : ∀ p ∈ Y, ∀ q ∈ V \ O, dist p q < d → CompNear (V \ O) d q b)
    (hsep : SepFrom V O a d) (hbC : b ∉ connectedComponentIn (V \ O) a) (hyY : y ∈ Y) :
    y ∉ connectedComponentIn (U \ O) x := by
  intro hy
  obtain ⟨hKP, -⟩ := transfer_core hd hVU hUV ha hb hx hX hY hXY hAX hAY hsep
  rcases hKP hy with (hC | ⟨-, hyX⟩) | ⟨hb', -⟩
  · have hn := hAY y hyY y (connectedComponentIn_subset _ _ hC) (by rw [dist_self]; exact hd)
    exact hbC (mem_comp_of_compNear hsep hb (hn.symm.of_mem_right hC))
  · have := hXY y hyX y hyY
    rw [dist_self] at this; linarith
  · exact hbC hb'

end LQGMetric.GM
