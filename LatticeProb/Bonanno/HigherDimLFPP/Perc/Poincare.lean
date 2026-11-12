/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.Poincare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Lattice
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The mod-2 discrete Poincaré lemma on `ℤ^d` (HA5 D7(i))

A `ℤ/2`-valued 1-cochain `ω` on the nearest-neighbour edges of `ℤ^d` (`ω x i` is the value on the
edge from `x` to `x + e_i`) whose sum around every plaquette vanishes is a coboundary:
`ω x i = φ (x + e_i) - φ x` for some `φ : ℤ^d → ℤ/2` (`poincareMod2`).

Proof (HA5 D7(i), explicit telescoping primitive). For `g : ℤ → ℤ/2` let `prim g` be the discrete
primitive with `prim g 0 = 0` and `prim g (a + 1) = prim g a + g a`. Let `x^{(n)}` keep the
coordinates of `x` of index `< n` and set the others to `0` (`truncBelow n x`), and put
`φ_n x = ∑_{j < n} prim (t ↦ ω (x^{(j)} + t e_j) j) (x_j)` (`potential ω n x`). By induction on `n`:
`φ_n (x + e_i) = φ_n x + ω (x^{(n)}) i` for `i < n`, and `φ_n (x + e_i) = φ_n x` for `i ≥ n`. In
the step for `i < n` the plaquette condition at `x^{(n)} + t e_n` turns the change of the new term
into the telescoping sum `prim (t ↦ r t + r (t+1)) (x_n) = r 0 + r x_n` with
`r t = ω (x^{(n)} + t e_n) i`. Then `φ := φ_d` works, since `x^{(d)} = x`. (The induction is HA5's
telescoping computation, organized one coordinate at a time.)
-/

set_option autoImplicit false

namespace HigherDimLFPP

namespace Perc

variable {d : ℕ}

/-! ### Arithmetic in `ℤ/2` -/

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  revert a b; decide

lemma zmod2_eq_add_of_eq_add {a b c : ZMod 2} (h : a = b + c) : b = a + c := by
  subst h; revert b c; decide

/-! ### The discrete primitive on `ℤ` -/

/-- Discrete primitive of `g : ℤ → ℤ/2`: `∑_{0 ≤ k < a} g k` for `a ≥ 0` and `∑_{a ≤ k < 0} g k`
for `a < 0`. -/
def prim (g : ℤ → ZMod 2) (a : ℤ) : ZMod 2 :=
  if 0 ≤ a then ∑ k ∈ Finset.range a.toNat, g k
  else ∑ k ∈ Finset.range (-a).toNat, g (-((k : ℤ) + 1))

lemma prim_zero (g : ℤ → ZMod 2) : prim g 0 = 0 := by
  simp [prim]

/-- For `a ≤ 0` the primitive is the sum over `a ≤ k < 0`. -/
lemma prim_of_nonpos (g : ℤ → ZMod 2) {a : ℤ} (ha : a ≤ 0) :
    prim g a = ∑ k ∈ Finset.range (-a).toNat, g (-((k : ℤ) + 1)) := by
  unfold prim
  split_ifs with h
  · have h0 : a = 0 := le_antisymm ha h
    subst h0
    simp
  · rfl

lemma prim_succ (g : ℤ → ZMod 2) (a : ℤ) : prim g (a + 1) = prim g a + g a := by
  rcases le_or_gt 0 a with ha | ha
  · have ha1 : 0 ≤ a + 1 := by omega
    have ht : (a + 1).toNat = a.toNat + 1 := by omega
    simp only [prim, ha, ha1, ↓reduceIte, ht, Finset.sum_range_succ]
    congr 2
    exact Int.toNat_of_nonneg ha
  · rw [prim_of_nonpos g (show a + 1 ≤ 0 by omega), prim_of_nonpos g ha.le]
    have ht : (-a).toNat = (-(a + 1)).toNat + 1 := by omega
    rw [ht, Finset.sum_range_succ]
    have hk : -(((-(a + 1)).toNat : ℕ) + 1 : ℤ) = a := by omega
    rw [hk]
    exact zmod2_eq_add_of_eq_add rfl

lemma prim_add (g h : ℤ → ZMod 2) (a : ℤ) :
    prim (fun t => g t + h t) a = prim g a + prim h a := by
  unfold prim
  split_ifs <;> exact Finset.sum_add_distrib

/-- The telescoping identity `prim (t ↦ r t + r (t+1)) a = r 0 + r a`. -/
lemma prim_telescope (r : ℤ → ZMod 2) (a : ℤ) :
    prim (fun t => r t + r (t + 1)) a = r 0 + r a := by
  induction a using Int.induction_on with
  | zero => rw [prim_zero, zmod2_add_self]
  | succ n ih =>
    rw [prim_succ, ih]
    generalize r 0 = p; generalize r n = q; generalize r (n + 1) = s
    revert p q s; decide
  | pred n ih =>
    have h := prim_succ (fun t => r t + r (t + 1)) (-(n : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    generalize prim (fun t => r t + r (t + 1)) (-(n : ℤ) - 1) = P at h ⊢
    generalize r 0 = p at h ⊢; generalize r (-(n : ℤ)) = q at h ⊢
    generalize r (-(n : ℤ) - 1) = s at h ⊢
    revert p q s P; decide

/-! ### Truncations -/

/-- `x^{(n)}`: keep the coordinates of index `< n`, set the others to `0`. -/
def truncBelow (n : ℕ) (x : Zd d) : Zd d := fun k => if k.val < n then x k else 0

lemma truncBelow_add_single_of_lt (n : ℕ) (x : Zd d) {i : Fin d} (hi : i.val < n) :
    truncBelow n (x + Pi.single i 1) = truncBelow n x + Pi.single i 1 := by
  funext k
  rw [add_single_apply]
  simp only [truncBelow]
  by_cases hk : k = i
  · subst hk
    simp only [hi, ↓reduceIte, add_single_apply_self]
  · rw [add_single_apply_of_ne x hk]
    simp only [hk, ↓reduceIte]

lemma truncBelow_add_single_of_le (n : ℕ) (x : Zd d) {i : Fin d} (hi : n ≤ i.val) :
    truncBelow n (x + Pi.single i 1) = truncBelow n x := by
  funext k
  simp only [truncBelow]
  by_cases hk : k = i
  · subst hk
    have : ¬ k.val < n := by omega
    simp only [this, ↓reduceIte]
  · rw [add_single_apply_of_ne x hk]

lemma truncBelow_succ (n : ℕ) (x : Zd d) (h : n < d) :
    truncBelow n x + Pi.single (⟨n, h⟩ : Fin d) (x ⟨n, h⟩) = truncBelow (n + 1) x := by
  funext k
  rw [add_single_apply]
  simp only [truncBelow]
  by_cases hk : k = ⟨n, h⟩
  · subst hk
    simp
  · have hkn : k.val ≠ n := fun h' => hk (Fin.ext h')
    by_cases hlt : k.val < n
    · have h2 : k.val < n + 1 := by omega
      simp only [hk, hlt, h2, ↓reduceIte]
    · have h2 : ¬ k.val < n + 1 := by omega
      simp only [hk, hlt, h2, ↓reduceIte]

lemma truncBelow_dim (x : Zd d) : truncBelow d x = x := by
  funext k
  simp [truncBelow, k.isLt]

/-! ### The potential -/

/-- The partial potential `φ_n x = ∑_{j < n} prim (t ↦ ω (x^{(j)} + t e_j) j) (x_j)`. -/
def potential (ω : Zd d → Fin d → ZMod 2) : ℕ → Zd d → ZMod 2
  | 0, _ => 0
  | n + 1, x => potential ω n x +
      if h : n < d then
        prim (fun t => ω (truncBelow n x + Pi.single (⟨n, h⟩ : Fin d) t) ⟨n, h⟩) (x ⟨n, h⟩)
      else 0

/-- `φ_n` does not see the coordinates of index `≥ n`. -/
lemma potential_add_single_of_le (ω : Zd d → Fin d → ZMod 2) :
    ∀ (n : ℕ) (x : Zd d) (i : Fin d), n ≤ i.val →
      potential ω n (x + Pi.single i 1) = potential ω n x := by
  intro n
  induction n with
  | zero => intro x i _; rfl
  | succ n ih =>
    intro x i hi
    simp only [potential]
    rw [ih x i (by omega)]
    congr 1
    split_ifs with h
    · have hne : (⟨n, h⟩ : Fin d) ≠ i := by
        intro h'
        rw [← h'] at hi
        simp at hi
      rw [truncBelow_add_single_of_le n x (by omega), add_single_apply_of_ne x hne]
    · rfl

/-- The key step: `φ_n (x + e_i) = φ_n x + ω (x^{(n)}) i` for `i < n ≤ d`. -/
lemma potential_add_single_of_lt (ω : Zd d → Fin d → ZMod 2)
    (hω : ∀ x i j, ω x i + ω (x + Pi.single i 1) j + ω (x + Pi.single j 1) i + ω x j = 0) :
    ∀ (n : ℕ), n ≤ d → ∀ (x : Zd d) (i : Fin d), i.val < n →
      potential ω n (x + Pi.single i 1) = potential ω n x + ω (truncBelow n x) i := by
  intro n
  induction n with
  | zero => intro _ x i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro hn x i hi
    have h : n < d := by omega
    simp only [potential, h, ↓reduceDIte]
    set j : Fin d := ⟨n, h⟩ with hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hin | hin
    · -- `i < n`: the plaquette condition and the telescoping identity
      have hij : j ≠ i := by
        intro h'
        rw [← h'] at hin
        simp [hj] at hin
      rw [ih (by omega) x i hin, truncBelow_add_single_of_lt n x hin, add_single_apply_of_ne x hij]
      have hplaq : ∀ t : ℤ,
          ω (truncBelow n x + Pi.single i 1 + Pi.single j t) j =
            ω (truncBelow n x + Pi.single j t) j +
              (ω (truncBelow n x + Pi.single j t) i +
                ω (truncBelow n x + Pi.single j (t + 1)) i) := by
        intro t
        have hp := hω (truncBelow n x + Pi.single j t) i j
        have e1 : truncBelow n x + Pi.single j t + Pi.single i 1 =
            truncBelow n x + Pi.single i 1 + Pi.single j t := add_right_comm _ _ _
        have e2 : truncBelow n x + Pi.single j t + Pi.single j 1 =
            truncBelow n x + Pi.single j (t + 1) := by
          rw [add_assoc, ← Pi.single_add]
        rw [e1, e2] at hp
        generalize ω (truncBelow n x + Pi.single i 1 + Pi.single j t) j = A at hp ⊢
        generalize ω (truncBelow n x + Pi.single j t) j = B at hp ⊢
        generalize ω (truncBelow n x + Pi.single j t) i = C at hp ⊢
        generalize ω (truncBelow n x + Pi.single j (t + 1)) i = E at hp ⊢
        revert A B C E; decide
      simp_rw [hplaq]
      have htel := prim_telescope (fun t => ω (truncBelow n x + Pi.single j t) i) (x j)
      beta_reduce at htel
      rw [prim_add, htel]
      simp only [Pi.single_zero, add_zero]
      rw [truncBelow_succ n x h]
      generalize potential ω n x = P
      generalize ω (truncBelow n x) i = Q
      generalize prim (fun t => ω (truncBelow n x + Pi.single j t) j) (x j) = T
      generalize ω (truncBelow (n + 1) x) i = U
      revert P Q T U; decide
    · -- `i = n`: only the new term changes
      have hij : i = j := Fin.ext hin
      subst hij
      rw [potential_add_single_of_le ω n x _ (by simp [hj]),
        truncBelow_add_single_of_le n x (by simp [hj]), add_single_apply_self, prim_succ,
        truncBelow_succ n x h]
      generalize potential ω n x = P
      generalize prim (fun t => ω (truncBelow n x + Pi.single j t) j) (x j) = T
      generalize ω (truncBelow (n + 1) x) j = U
      revert P T U; decide

/-- **D7(i): the mod-2 discrete Poincaré lemma.** -/
theorem poincareMod2 (d : ℕ) : PoincareMod2 d := by
  intro ω hω
  refine ⟨potential ω d, fun x i => ?_⟩
  rw [potential_add_single_of_lt ω hω d le_rfl x i i.isLt, truncBelow_dim, zmod2_sub_eq_add]
  generalize potential ω d x = P
  generalize ω x i = Q
  revert P Q; decide

end Perc

end HigherDimLFPP
