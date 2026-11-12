/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.Exclusive at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.StepSum
import LatticeProb.Bonanno.LQGMetric.Perc.DualityMain

/-!
# Exclusivity half of planar duality

`perc_not_goodLR_and_badTB`: in the `K × L` rectangle a left–right crossing by a `4`-path of
good sites and a top–bottom crossing by a `*`-path of bad sites cannot both exist. With
`percGoodLR_or_percBadTB` this gives exactly one of the two. Consequence
`percGoodLR_meets_percBadTB`: a left–right `4`-crossing of sites in `A` and a top–bottom
`*`-crossing of sites in `C` of the same rectangle share a site (in particular a left–right
and a top–bottom `4`-crossing meet), which is what gluing crossings into circuits uses
(DDDF arXiv:1904.08021 Prop. 4.18 step 4, Ding–Dunlap arXiv:1812.06921 Prop. 4.2 Fig. 4,
Ding–Gwynne arXiv:1807.01072 Prop. 3.9).

## Proof (crossing parity)

Let `P` be the good path, run from `(K, ·)` (one extra site right of the rectangle) back to
column `0`. For a site `x = (c, j)` let `π x` be the number of steps of `P` crossing the
vertical line between columns `c` and `c + 1` below row `j` (the downward ray from the right
edge of `x`). Counting the steps of `P` crossing the boundary of a half-column
`{c + 1} × (-∞, m)` (an even number, since both ends of `P` are outside it,
`percStepSum_cross_even`) shows that `π x ≡ π y (mod 2)` for `*`-adjacent sites `x, y` off
`P`; `π = 0` on the bottom row and `π` is odd on the top row (the line between columns `c` and
`c + 1` separates the two ends of `P`). A bad `*`-path from the top to the bottom row would
change the parity. This is the discrete form of the ray-crossing parity proof of the polygonal
Jordan curve theorem (e.g. Courant–Robbins, *What is mathematics?*, Ch. V §3.3); the lattice
write-up is our own (DEVIATIONS: own elementary proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

namespace PercExcl

/-- Steps of a `4`-path with both endpoints in rows `0, …, L-1`. -/
def RowStep (L : ℤ) (u v : ℤ × ℤ) : Prop :=
  PercAdj4 u v ∧ 0 ≤ u.2 ∧ u.2 < L ∧ 0 ≤ v.2 ∧ v.2 < L

/-- Horizontal step between columns `c` and `c + 1` below row `j`. -/
def wH (c j : ℤ) (u v : ℤ × ℤ) : ℕ :=
  if ((u.1 = c ∧ v.1 = c + 1) ∨ (u.1 = c + 1 ∧ v.1 = c)) ∧ u.2 < j then 1 else 0

/-- Horizontal step between `(c, j)` and `(c + 1, j)`. -/
def wHrow (c j : ℤ) (u v : ℤ × ℤ) : ℕ :=
  if ((u.1 = c ∧ v.1 = c + 1) ∨ (u.1 = c + 1 ∧ v.1 = c)) ∧ u.2 = j ∧ v.2 = j then 1 else 0

/-- Vertical step between `(col, m - 1)` and `(col, m)`. -/
def wV (col m : ℤ) (u v : ℤ × ℤ) : ℕ :=
  if u.1 = col ∧ v.1 = col ∧ ((u.2 = m - 1 ∧ v.2 = m) ∨ (u.2 = m ∧ v.2 = m - 1)) then 1 else 0

lemma stepSum_zero_fun : ∀ l : List (ℤ × ℤ), percStepSum (fun _ _ => 0) l = 0
  | [] => rfl
  | [_] => rfl
  | _ :: v :: t => by rw [percStepSum_cons_cons, stepSum_zero_fun (v :: t)]

variable {K L : ℤ} {p : List (ℤ × ℤ)}

lemma split (hc : p.IsChain (RowStep L)) (c j j' : ℤ) (hj : j' = j + 1) :
    percStepSum (wH c j') p = percStepSum (wH c j) p + percStepSum (wHrow c j) p := by
  rw [← percStepSum_add]
  refine percStepSum_congr (fun u v h => ?_) p hc
  obtain ⟨ha, -⟩ := h
  simp only [PercAdj4] at ha
  simp only [wH, wHrow]
  split_ifs <;> omega

lemma Hrow_zero {c j : ℤ} {x : ℤ × ℤ} (hx : x ∉ p) (hxx : (x.1 = c ∨ x.1 = c + 1) ∧ x.2 = j) :
    percStepSum (wHrow c j) p = 0 := by
  refine percStepSum_eq_zero (fun u v hw => ?_) p hx
  simp only [wHrow] at hw
  split_ifs at hw with hh
  · rw [Prod.ext_iff, Prod.ext_iff]; omega
  · exact absurd rfl hw

lemma V_zero {col m : ℤ} {x : ℤ × ℤ} (hx : x ∉ p) (hxx : x.1 = col ∧ (x.2 = m ∨ x.2 = m - 1)) :
    percStepSum (wV col m) p = 0 := by
  refine percStepSum_eq_zero (fun u v hw => ?_) p hx
  simp only [wV] at hw
  split_ifs at hw with hh
  · rw [Prod.ext_iff, Prod.ext_iff]; omega
  · exact absurd rfl hw

variable {u0 : ℤ × ℤ} {t : List (ℤ × ℤ)}

/-- Crossings of the boundary of the half-column `{c + 1} × (-∞, m)`. -/
lemma half (hc : (u0 :: t).IsChain (RowStep L)) (h0 : u0.1 = K)
    (hl : ((u0 :: t).getLast (List.cons_ne_nil _ _)).1 = 0) (c m : ℤ) (hc0 : 0 ≤ c)
    (hcK : c + 1 < K) :
    Even (percStepSum (wH c m) (u0 :: t) + percStepSum (wH (c + 1) m) (u0 :: t) +
      percStepSum (wV (c + 1) m) (u0 :: t)) := by
  classical
  set S : ℤ × ℤ → Prop := fun z => z.1 = c + 1 ∧ z.2 < m with hS
  have e : percStepSum (percCross S) (u0 :: t) = percStepSum
      (fun u v => (wH c m u v + wH (c + 1) m u v) + wV (c + 1) m u v) (u0 :: t) := by
    refine percStepSum_congr (fun u v h => ?_) _ hc
    obtain ⟨ha, -⟩ := h
    simp only [PercAdj4] at ha
    simp only [percCross, wH, wV, hS]
    split_ifs <;> omega
  rw [percStepSum_add, percStepSum_add] at e
  rw [← e, percStepSum_cross_even S t u0]
  exact iff_of_false (by simp only [hS]; omega) (by simp only [hS]; omega)

/-- The line between columns `c` and `c + 1` separates the two ends. -/
lemma line (hc : (u0 :: t).IsChain (RowStep L)) (h0 : u0.1 = K)
    (hl : ((u0 :: t).getLast (List.cons_ne_nil _ _)).1 = 0) (c : ℤ) (hc0 : 0 ≤ c)
    (hcK : c < K) : ¬ Even (percStepSum (wH c L) (u0 :: t)) := by
  classical
  set S : ℤ × ℤ → Prop := fun z => z.1 ≤ c with hS
  have e : percStepSum (percCross S) (u0 :: t) = percStepSum (wH c L) (u0 :: t) := by
    refine percStepSum_congr (fun u v h => ?_) _ hc
    obtain ⟨ha, -, h2, -, -⟩ := h
    simp only [PercAdj4] at ha
    simp only [percCross, wH, hS]
    split_ifs <;> omega
  rw [← e, percStepSum_cross_even S t u0]
  simp only [hS]
  omega

lemma bottom (hc : p.IsChain (RowStep L)) (c : ℤ) : percStepSum (wH c 0) p = 0 := by
  rw [percStepSum_congr (w' := fun _ _ => 0) (fun u v h => ?_) p hc, stepSum_zero_fun]
  obtain ⟨-, h1, -⟩ := h
  simp only [wH]
  split_ifs <;> omega

end PercExcl

end LQGMetric
