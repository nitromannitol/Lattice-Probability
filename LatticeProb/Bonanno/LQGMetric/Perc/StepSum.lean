/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.StepSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Ring

/-!
# Weighted step counts along lists of sites, and the parity of boundary crossings

For a list of sites `l = [v₀, …, v_m]` and a weight `w` on ordered pairs of sites,
`percStepSum w l = ∑ᵢ w vᵢ vᵢ₊₁`. The basic fact used for the exclusivity half of planar
duality (`LQGMetric.Perc.Exclusive`) is `percStepSum_cross_even`: the number of steps of a list
crossing the boundary of a set `S` (one endpoint in `S`, the other not) is even iff both
endpoints of the list are on the same side of `S` (the discrete form of the ray-crossing parity
argument for the polygonal Jordan curve theorem; own elementary write-up).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

/-- `∑ᵢ w vᵢ vᵢ₊₁` along the list `[v₀, …, v_m]`. -/
def percStepSum (w : ℤ × ℤ → ℤ × ℤ → ℕ) : List (ℤ × ℤ) → ℕ
  | u :: v :: t => w u v + percStepSum w (v :: t)
  | _ => 0

lemma percStepSum_cons_cons (w : ℤ × ℤ → ℤ × ℤ → ℕ) (u v : ℤ × ℤ) (t : List (ℤ × ℤ)) :
    percStepSum w (u :: v :: t) = w u v + percStepSum w (v :: t) := rfl

lemma percStepSum_add (w₁ w₂ : ℤ × ℤ → ℤ × ℤ → ℕ) : ∀ l : List (ℤ × ℤ),
    percStepSum (fun u v => w₁ u v + w₂ u v) l = percStepSum w₁ l + percStepSum w₂ l
  | [] => rfl
  | [_] => rfl
  | u :: v :: t => by
    simp only [percStepSum_cons_cons, percStepSum_add w₁ w₂ (v :: t)]
    ring

lemma percStepSum_congr {R : ℤ × ℤ → ℤ × ℤ → Prop} {w w' : ℤ × ℤ → ℤ × ℤ → ℕ}
    (h : ∀ u v, R u v → w u v = w' u v) : ∀ l : List (ℤ × ℤ), l.IsChain R →
    percStepSum w l = percStepSum w' l
  | [], _ => rfl
  | [_], _ => rfl
  | u :: v :: t, hc => by
    rw [List.isChain_cons_cons] at hc
    simp only [percStepSum_cons_cons, h u v hc.1, percStepSum_congr h (v :: t) hc.2]

/-- If every step of positive weight has `x` as an endpoint and `x` is not on the list, the
weighted step count vanishes. -/
lemma percStepSum_eq_zero {w : ℤ × ℤ → ℤ × ℤ → ℕ} {x : ℤ × ℤ}
    (h : ∀ u v, w u v ≠ 0 → u = x ∨ v = x) : ∀ l : List (ℤ × ℤ), x ∉ l →
    percStepSum w l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | u :: v :: t, hx => by
    simp only [List.mem_cons, not_or] at hx
    rw [percStepSum_cons_cons, percStepSum_eq_zero h (v :: t)
      (by simp only [List.mem_cons, not_or]; exact ⟨hx.2.1, hx.2.2⟩)]
    by_contra hne
    rcases h u v (by omega) with h' | h'
    · exact hx.1 h'.symm
    · exact hx.2.1 h'.symm

/-- The crossing indicator of the boundary of `S`. -/
def percCross (S : ℤ × ℤ → Prop) [DecidablePred S] (u v : ℤ × ℤ) : ℕ :=
  if S u then (if S v then 0 else 1) else (if S v then 1 else 0)

/-- Parity of the number of boundary crossings of `S` along a list. -/
lemma percStepSum_cross_even (S : ℤ × ℤ → Prop) [DecidablePred S] :
    ∀ (t : List (ℤ × ℤ)) (u : ℤ × ℤ), Even (percStepSum (percCross S) (u :: t)) ↔
      (S u ↔ S ((u :: t).getLast (List.cons_ne_nil _ _)))
  | [], u => by simp [percStepSum]
  | v :: t, u => by
    rw [percStepSum_cons_cons, List.getLast_cons_cons]
    have ih := percStepSum_cross_even S t v
    have key : percCross S u v = if (S u ↔ S v) then 0 else 1 := by
      unfold percCross
      by_cases hu : S u <;> by_cases hv : S v <;> simp [hu, hv]
    rw [key]
    by_cases h : (S u ↔ S v)
    · simp only [h, ↓reduceIte, zero_add]
      rw [ih]
    · simp only [h, ↓reduceIte]
      rw [add_comm, Nat.even_add_one, ih]
      tauto

end LQGMetric
