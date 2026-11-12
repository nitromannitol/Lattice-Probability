/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.Duality at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Perc.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ring

/-!
`percGoodLR_or_percBadTB`: for every colouring `good : ℤ × ℤ → Prop` of the sites of the
`K × L` rectangle (`K, L ≥ 1`), there is a left–right crossing by a `4`-path of good sites or a
top–bottom crossing by a `*`-path of bad sites. This is the "planar duality" used by Ding–Gwynne
(arXiv:1807.01072, proof of Lemma 3.11, `metric-comparison-final.tex` line 1267), by
Ding–Dunlap (arXiv:1812.06921, proof of Prop. 4.2, `tightness-gg.tex` line 2716, there with the
roles of `4` and `*` exchanged; a `4`-path is a `*`-path so our good crossing is also a king path)
and by DDDF (arXiv:1904.08021, proof of Prop. 4.18 step 1, `tightness.tex` line 895).

We follow the classical exploration-path proof of the Hex theorem (D. Gale, *The game of Hex
and the Brouwer fixed-point theorem*, Amer. Math. Monthly 86 (1979), §2; for site percolation on
the matching pair (`ℤ²`, `ℤ²*`) see Kesten, *Percolation theory for mathematicians* (1982),
§2.4, and Grimmett, *Percolation*, 2nd ed., §11.2 / Lemma 11.21). The rectangle is framed: the
columns `-1` and `K` (rows `0, …, L-1`) are good and the rows `-1` and `L` (columns
`-1, …, K`) are bad. A state is an interface edge, i.e. a pair `(g, b)` of `4`-adjacent sites
of the frame with `g` good and `b` bad; we walk along the interface keeping good on the right.
The direction of motion is `f = rot_cw (b - g)`; the two sites ahead are `g + f`, `b + f`:

* `g + f` bad: turn right, new state `(g, g + f)`;
* `g + f` good, `b + f` bad: go straight, new state `(g + f, b + f)`;
* `g + f` good, `b + f` good: turn left, new state `(b + f, b)`.

(In the checkerboard case the bad diagonal is joined and the good one is separated, which is
the rule for good = `4`-connected, bad = `*`-connected.) The step map has an explicit left
inverse `pred` on interface edges, so it is injective; the start edge (top-left corner) has no
predecessor. Since the frame is finite, the walk started at the top-left corner reaches an edge
with `g` in column `K` or `b` in row `-1`. Along the walk, `g` stays `4`-connected through good
frame sites to the left column and `b` stays `*`-connected through bad frame sites to the top
row, which gives the two crossings.

The formal argument (left inverse, termination by pigeonhole) is our own write-up of this
standard proof (DEVIATIONS: own elementary proof of a classical fact).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

namespace PercDual

variable (K L : ℤ) (good : ℤ × ℤ → Prop)

/-- The framed rectangle `[-1, K] × [-1, L]`. -/
def inE (x : ℤ × ℤ) : Prop := -1 ≤ x.1 ∧ x.1 ≤ K ∧ -1 ≤ x.2 ∧ x.2 ≤ L

/-- Good sites of the frame: good grid sites and the side columns `-1`, `K`. -/
def goodE (x : ℤ × ℤ) : Prop :=
  -1 ≤ x.1 ∧ x.1 ≤ K ∧ 0 ≤ x.2 ∧ x.2 < L ∧ (x.1 = -1 ∨ x.1 = K ∨ good x)

/-- Bad sites of the frame. -/
def badE (x : ℤ × ℤ) : Prop := inE K L x ∧ ¬ goodE K L good x

/-- Interface edges: `4`-adjacent pairs (good, bad) of frame sites. -/
def IsIface (s : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  goodE K L good s.1 ∧ badE K L good s.2 ∧ PercAdj4 s.1 s.2

open Classical in
/-- One step of the exploration walk. -/
noncomputable def step (s : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  if goodE K L good (s.1.1 + (s.2.2 - s.1.2), s.1.2 + (s.1.1 - s.2.1)) then
    (if goodE K L good (s.2.1 + (s.2.2 - s.1.2), s.2.2 + (s.1.1 - s.2.1)) then
      ((s.2.1 + (s.2.2 - s.1.2), s.2.2 + (s.1.1 - s.2.1)), s.2)
    else ((s.1.1 + (s.2.2 - s.1.2), s.1.2 + (s.1.1 - s.2.1)),
      (s.2.1 + (s.2.2 - s.1.2), s.2.2 + (s.1.1 - s.2.1))))
  else (s.1, (s.1.1 + (s.2.2 - s.1.2), s.1.2 + (s.1.1 - s.2.1)))

open Classical in
/-- The left inverse of `step` on interface edges. -/
noncomputable def pred (s : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  if badE K L good (s.1.1 - (s.2.2 - s.1.2), s.1.2 - (s.1.1 - s.2.1)) then
    (s.1, (s.1.1 - (s.2.2 - s.1.2), s.1.2 - (s.1.1 - s.2.1)))
  else if goodE K L good (s.2.1 - (s.2.2 - s.1.2), s.2.2 - (s.1.1 - s.2.1)) then
    ((s.2.1 - (s.2.2 - s.1.2), s.2.2 - (s.1.1 - s.2.1)), s.2)
  else ((s.1.1 - (s.2.2 - s.1.2), s.1.2 - (s.1.1 - s.2.1)),
    (s.2.1 - (s.2.2 - s.1.2), s.2.2 - (s.1.1 - s.2.1)))

variable {K L good}

lemma goodE_bounds {x : ℤ × ℤ} (h : goodE K L good x) :
    -1 ≤ x.1 ∧ x.1 ≤ K ∧ 0 ≤ x.2 ∧ x.2 < L :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

lemma badE_cases {x : ℤ × ℤ} (h : badE K L good x) :
    inE K L x ∧ (x.2 = -1 ∨ x.2 = L ∨ (0 ≤ x.1 ∧ x.1 < K)) := by
  refine ⟨h.1, ?_⟩
  obtain ⟨⟨h1, h2, h3, h4⟩, hg⟩ := h
  by_contra hc
  exact hg ⟨h1, h2, by omega, by omega, by omega⟩

/-- A bad frame site in a row `0 ≤ j < L` is a bad grid site. -/
lemma badE_mid {x : ℤ × ℤ} (h : badE K L good x) (h0 : 0 ≤ x.2) (h1 : x.2 < L) :
    percInGrid K L x ∧ ¬ good x := by
  obtain ⟨⟨a1, a2, a3, a4⟩, hg⟩ := h
  have hx : 0 ≤ x.1 ∧ x.1 < K := by
    by_contra hc
    exact hg ⟨a1, a2, h0, h1, by omega⟩
  exact ⟨⟨hx.1, hx.2, h0, h1⟩, fun hgx => hg ⟨a1, a2, h0, h1, Or.inr (Or.inr hgx)⟩⟩

/-- A good frame site off the side columns is a good grid site. -/
lemma goodE_mid {x : ℤ × ℤ} (h : goodE K L good x) (h0 : x.1 ≠ -1) (h1 : x.1 ≠ K) :
    percInGrid K L x ∧ good x := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  refine ⟨⟨by omega, by omega, a3, a4⟩, ?_⟩
  rcases a5 with h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · exact h

/-- `step` has the left inverse `pred` on interface edges. -/
lemma pred_step {s : (ℤ × ℤ) × (ℤ × ℤ)} (hs : IsIface K L good s) :
    pred K L good (step K L good s) = s := by
  obtain ⟨⟨g1, g2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨hg, hb, hadj⟩ := hs
  simp only at hg hb hadj
  rw [step]
  dsimp only
  split_ifs with h1 h2
  · -- left turn
    have c1 : ¬ badE K L good (b1 + (b2 - g2) - (b2 - (b2 + (g1 - b1))),
        b2 + (g1 - b1) - (b1 + (b2 - g2) - b1)) := by
      intro h; apply h.2; convert h1 using 2 <;> ring
    have c2 : goodE K L good (b1 - (b2 - (b2 + (g1 - b1))), b2 - (b1 + (b2 - g2) - b1)) := by
      convert hg using 2 <;> ring
    rw [pred]; dsimp only; rw [ite_eq_right c1, ite_eq_left c2]
    ext <;> dsimp only <;> ring
  · -- straight
    have c1 : ¬ badE K L good (g1 + (b2 - g2) - (b2 + (g1 - b1) - (g2 + (g1 - b1))),
        g2 + (g1 - b1) - (g1 + (b2 - g2) - (b1 + (b2 - g2)))) := by
      intro h; apply h.2; convert hg using 2 <;> ring
    have c2 : ¬ goodE K L good (b1 + (b2 - g2) - (b2 + (g1 - b1) - (g2 + (g1 - b1))),
        b2 + (g1 - b1) - (g1 + (b2 - g2) - (b1 + (b2 - g2)))) := by
      intro h; apply hb.2; convert h using 2 <;> ring
    rw [pred]; dsimp only; rw [ite_eq_right c1, ite_eq_right c2]
    ext <;> dsimp only <;> ring
  · -- right turn
    have c1 : badE K L good (g1 - (g2 + (g1 - b1) - g2), g2 - (g1 - (g1 + (b2 - g2)))) := by
      convert hb using 2 <;> ring
    rw [pred]; dsimp only; rw [ite_eq_left c1]
    ext <;> dsimp only <;> ring

variable (K L good) in
/-- One step of a `4`-path through good frame sites. -/
def StepGE (x y : ℤ × ℤ) : Prop := goodE K L good x ∧ goodE K L good y ∧ PercAdj4 x y

variable (K L good) in
/-- One step of a `*`-path through bad frame sites. -/
def StepBE (x y : ℤ × ℤ) : Prop := badE K L good x ∧ badE K L good y ∧ PercAdjK x y

variable (K L good) in
/-- `g` is joined to the left column `-1` by a `4`-path of good frame sites. -/
def GR (g : ℤ × ℤ) : Prop :=
  ∃ w : ℤ × ℤ, w.1 = -1 ∧ 0 ≤ w.2 ∧ w.2 < L ∧ Relation.ReflTransGen (StepGE K L good) w g

variable (K L good) in
/-- `b` is joined to the top row `L` by a `*`-path of bad frame sites. -/
def BR (b : ℤ × ℤ) : Prop :=
  ∃ w : ℤ × ℤ, w.2 = L ∧ -1 ≤ w.1 ∧ w.1 ≤ K ∧ Relation.ReflTransGen (StepBE K L good) w b

variable (K L good) in
/-- The invariant of the exploration walk. -/
def Inv (s : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  IsIface K L good s ∧ GR K L good s.1 ∧ BR K L good s.2

/-- The invariant is preserved by a step from a state with `g` off column `K` and `b` off
row `-1`. -/
lemma inv_step {s : (ℤ × ℤ) × (ℤ × ℤ)} (hs : Inv K L good s) (h1K : s.1.1 ≠ K)
    (h2 : s.2.2 ≠ -1) : Inv K L good (step K L good s) := by
  obtain ⟨⟨g1, g2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨⟨hg, hb, hadj⟩, ⟨w, hw1, hw2, hw3, hwg⟩, ⟨v, hv1, hv2, hv3, hvb⟩⟩ := hs
  simp only at hg hb hadj hwg hvb h1K h2
  have bg := goodE_bounds hg
  have cb := badE_cases hb
  simp only [inE] at cb
  simp only [PercAdj4] at hadj
  rw [step]; dsimp only
  split_ifs with c1 c2
  · -- left turn: new state `(b + f, b)`
    have bg' := goodE_bounds c2
    refine ⟨⟨c2, hb, ?_⟩, ⟨w, hw1, hw2, hw3, ?_⟩, ⟨v, hv1, hv2, hv3, hvb⟩⟩
    · simp only [PercAdj4]; omega
    · refine (hwg.tail ⟨hg, c1, ?_⟩).tail ⟨c1, c2, ?_⟩ <;> simp only [PercAdj4] <;> omega
  · -- straight: new state `(g + f, b + f)`
    have hin : inE K L (b1 + (b2 - g2), b2 + (g1 - b1)) := by
      simp only [inE]; omega
    refine ⟨⟨c1, ⟨hin, c2⟩, ?_⟩, ⟨w, hw1, hw2, hw3, hwg.tail ⟨hg, c1, ?_⟩⟩,
      ⟨v, hv1, hv2, hv3, hvb.tail ⟨hb, ⟨hin, c2⟩, ?_⟩⟩⟩
    · simp only [PercAdj4]; omega
    · simp only [PercAdj4]; omega
    · simp only [PercAdjK]; omega
  · -- right turn: new state `(g, g + f)`
    have hin : inE K L (g1 + (b2 - g2), g2 + (g1 - b1)) := by
      simp only [inE]; omega
    refine ⟨⟨hg, ⟨hin, c1⟩, ?_⟩, ⟨w, hw1, hw2, hw3, hwg⟩,
      ⟨v, hv1, hv2, hv3, hvb.tail ⟨hb, ⟨hin, c1⟩, ?_⟩⟩⟩
    · simp only [PercAdj4]; omega
    · simp only [PercAdjK]; omega

variable (L) in
/-- The start edge at the top-left corner. -/
def start : (ℤ × ℤ) × (ℤ × ℤ) := ((-1, L - 1), (-1, L))

lemma inv_start (hK : 0 ≤ K) (hL : 1 ≤ L) : Inv K L good (start L) := by
  have hg : goodE K L good (-1, L - 1) := ⟨le_rfl, by omega, by omega, by omega, Or.inl rfl⟩
  have hb : badE K L good (-1, L) := ⟨⟨le_rfl, by omega, by omega, le_rfl⟩,
    fun h => by have := h.2.2.2.1; simp at this⟩
  refine ⟨⟨hg, hb, ?_⟩, ⟨(-1, L - 1), rfl, by simp; omega, by simp,
    Relation.ReflTransGen.refl⟩, ⟨(-1, L), rfl, le_rfl, by simp; omega,
    Relation.ReflTransGen.refl⟩⟩
  refine Or.inl ⟨rfl, Or.inr ?_⟩
  show L = L - 1 + 1
  omega

lemma not_iface_pred_start : ¬ IsIface K L good (pred K L good (start L)) := by
  intro h
  rw [pred, start] at h
  dsimp only at h
  have hn1 : ¬ badE K L good (-1 - (L - (L - 1)), L - 1 - (-1 - -1)) :=
    fun h' => by have := h'.1.1; simp at this
  have hn2 : ¬ goodE K L good (-1 - (L - (L - 1)), L - (-1 - -1)) :=
    fun h' => by have := h'.1; simp at this
  rw [ite_eq_right hn1, ite_eq_right hn2] at h
  have := h.1.1
  simp at this

end PercDual

end LQGMetric
