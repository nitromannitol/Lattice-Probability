/-
# Pólya's recurrence theorem for the simple random walk on `ℤ²`

Moved from `manhattan-formalization`
(`Manhattan.Paper.Ergodic.{Recurrence,Rotation,Factorize,OneD,CentralBinom,
Harmonic,Assemble,Polya}`), where it was the one named input,
`SimpleRandomWalkRecurrent`, that the paper's own reduction of an alternating
directed environment to the plain simple random walk did not prove, because
Mathlib has no recurrence theorem for random walks. Only the part of the
source files with no reference to that paper's directed-lattice model is
ported here; the reduction itself (halving coordinates on the alternating
environment) stays behind.

The proof has four steps.

1. `rot_vec`/`eq_zero_iff_rot`: the map `(x, y) ↦ (x + y, x - y)` carries the
   four unit steps `(±1, 0), (0, ±1)` to the four diagonal steps `(±1, ±1)`,
   whose coordinates move independently. So a length-`n` word in the four
   steps is exactly a pair of length-`n` words of signs, and the walk returns
   to the origin exactly when both sign words do (`sum_vec_eq_zero_iff`).
2. `srwCount_eq_sq`: counting is then multiplicative, so the number of
   returning length-`n` words is the square of `oneDCount n`, the number of
   length-`n` sign words summing to zero.
3. `oneDCount_two_mul`: among the `2 ^ (2m)` sign words of length `2m`,
   exactly `C(2m, m) = ` `Nat.centralBinom m` sum to zero (half the entries
   `+1`, the rest `-1`, so a word is a choice of which half).
4. `sixteen_pow_le`: a sharp induction gives `16 ^ m ≤ 4 * m * centralBinom
   m ^ 2`, one full power of `m` stronger than Mathlib's own
   `Nat.four_pow_le_two_mul_self_mul_centralBinom`. That extra power is what
   turns the `m`-th even return probability into a term `≳ 1 / m` rather than
   `≳ 1 / m ^ 2`, so the Green series `∑ srwKernel n` is bounded below by a
   divergent harmonic series (`tsum_harmonic_eq_top`) instead of a convergent
   one: this is exactly the difference between recurrence and transience.
-/
import Mathlib

namespace LatticeProb

open scoped NNReal ENNReal

/-! ### The four steps of the simple random walk -/

/-- The four unit steps of the two-dimensional simple random walk. -/
inductive Step
  | east | north | west | south
  deriving DecidableEq, Fintype, Inhabited

/-- The displacement of a step. -/
def Step.vec : Step → ℤ × ℤ
  | .east => (1, 0)
  | .north => (0, 1)
  | .west => (-1, 0)
  | .south => (0, -1)

/-- The number of `n`-step simple-random-walk paths carrying `T` to the origin. -/
def srwCount (n : ℕ) (T : ℤ × ℤ) : ℕ :=
  ∑ e : Fin n → Step, if T + ∑ k, (e k).vec = 0 then 1 else 0

/-- Only the empty word carries `T` to the origin in zero steps, and only when
`T` is already the origin. -/
theorem srwCount_zero (T : ℤ × ℤ) : srwCount 0 T = if T = 0 then 1 else 0 := by
  simp [srwCount]

/-- Splitting off the first step of a length-`(n+1)` word. -/
theorem srwCount_succ (n : ℕ) (T : ℤ × ℤ) :
    srwCount (n + 1) T = ∑ s : Step, srwCount n (T + s.vec) := by
  have hsplit :
      ∑ e : Fin (n + 1) → Step, (if T + ∑ k, (e k).vec = 0 then 1 else 0) =
        ∑ p : Step × (Fin n → Step),
          (if T + ∑ k, ((Fin.cons p.1 p.2 : Fin (n + 1) → Step) k).vec = 0 then 1 else 0) :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Step)
      (fun p => if T + ∑ k, ((Fin.cons p.1 p.2 : Fin (n + 1) → Step) k).vec = 0 then 1 else 0)
      (fun e => if T + ∑ k, (e k).vec = 0 then 1 else 0) fun _ => rfl).symm
  rw [srwCount, hsplit, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [srwCount]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fin.sum_univ_succ]
  simp [← add_assoc]

/-- The return probability of the two-dimensional simple random walk after
`n` steps. -/
noncomputable def srwKernel (n : ℕ) : ℝ≥0 := (4 : ℝ≥0)⁻¹ ^ n * (srwCount n 0 : ℝ≥0)

/-- The walk is at the origin with probability `1` after zero steps. -/
theorem srwKernel_zero : srwKernel 0 = 1 := by
  rw [srwKernel, srwCount_zero]
  simp

/-- **Pólya's theorem in two dimensions**, stated as a proposition: the Green
series of the simple random walk on `ℤ²` diverges. Mathlib has no recurrence
theorem for random walks, so `LatticeProb.simpleRandomWalkRecurrent` below is
the first proof of an instance of it. -/
def SimpleRandomWalkRecurrent : Prop := ∑' n : ℕ, (srwKernel n : ℝ≥0∞) = ⊤

/-! ### The `45°` rotation that splits the walk into two independent coordinates -/

/-- The pair of signs a step carries in rotated coordinates, under the map
`(x, y) ↦ (x + y, x - y)`. -/
def Step.sgn : Step → Bool × Bool
  | .east => (true, true)
  | .north => (true, false)
  | .west => (false, false)
  | .south => (false, true)

/-- The step with a given pair of rotated signs. -/
def Step.ofSgn : Bool × Bool → Step
  | (true, true) => .east
  | (true, false) => .north
  | (false, false) => .west
  | (false, true) => .south

/-- A step is exactly a pair of signs. -/
def stepEquivSigns : Step ≃ Bool × Bool where
  toFun := Step.sgn
  invFun := Step.ofSgn
  left_inv s := by cases s <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- `true` counts `+1`, `false` counts `-1`. -/
def sgnVal (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem sgnVal_true : sgnVal true = 1 := rfl
@[simp] theorem sgnVal_false : sgnVal false = -1 := rfl

/-- The rotation sends a step's displacement to its pair of signs. -/
theorem rot_vec (s : Step) :
    (s.vec.1 + s.vec.2 = sgnVal s.sgn.1) ∧ (s.vec.1 - s.vec.2 = sgnVal s.sgn.2) := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- A displacement vanishes exactly when both rotated coordinates do. The
rotation is injective because its determinant is `-2 ≠ 0`, and `ℤ` is
torsion-free, which is what the doubling argument here uses. -/
theorem eq_zero_iff_rot (A B : ℤ) : (A, B) = (0, 0) ↔ A + B = 0 ∧ A - B = 0 := by
  constructor
  · rintro h
    have h1 : A = 0 := congrArg Prod.fst h
    have h2 : B = 0 := congrArg Prod.snd h
    subst h1; subst h2; exact ⟨by ring, by ring⟩
  · rintro ⟨h1, h2⟩
    have hA : (2 : ℤ) * A = 0 := by linarith
    have hB : (2 : ℤ) * B = 0 := by linarith
    have hA' : A = 0 := by linarith
    have hB' : B = 0 := by linarith
    subst hA'; subst hB'; rfl

/-! ### The planar return count is a square -/

/-- A word of steps is exactly a pair of sign words. -/
def wordEquiv (n : ℕ) : (Fin n → Step) ≃ (Fin n → Bool) × (Fin n → Bool) where
  toFun e := (fun k => (e k).sgn.1, fun k => (e k).sgn.2)
  invFun p := fun k => Step.ofSgn (p.1 k, p.2 k)
  left_inv e := by funext k; cases h : e k <;> simp [Step.ofSgn, Step.sgn, h]
  right_inv p := by
    apply Prod.ext <;> funext k <;>
      cases h1 : p.1 k <;> cases h2 : p.2 k <;>
        simp [Step.ofSgn, Step.sgn, h1, h2]

/-- The first coordinate of `wordEquiv` reads off the first rotated sign. -/
@[simp] theorem wordEquiv_fst (n : ℕ) (e : Fin n → Step) (k : Fin n) :
    (wordEquiv n e).1 k = (e k).sgn.1 := rfl

/-- The second coordinate of `wordEquiv` reads off the second rotated sign. -/
@[simp] theorem wordEquiv_snd (n : ℕ) (e : Fin n → Step) (k : Fin n) :
    (wordEquiv n e).2 k = (e k).sgn.2 := rfl

/-- The walk returns to the origin exactly when both rotated coordinates do. -/
theorem sum_vec_eq_zero_iff (n : ℕ) (e : Fin n → Step) :
    (∑ k, (e k).vec) = 0 ↔
      (∑ k, sgnVal ((wordEquiv n e).1 k) = 0) ∧ (∑ k, sgnVal ((wordEquiv n e).2 k) = 0) := by
  have hfst : (∑ k, (e k).vec).1 = ∑ k, ((e k).vec).1 := Prod.fst_sum
  have hsnd : (∑ k, (e k).vec).2 = ∑ k, ((e k).vec).2 := Prod.snd_sum
  have hsum1 : ∑ k, sgnVal ((wordEquiv n e).1 k)
      = (∑ k, ((e k).vec).1) + (∑ k, ((e k).vec).2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => ((rot_vec (e k)).1).symm
  have hsum2 : ∑ k, sgnVal ((wordEquiv n e).2 k)
      = (∑ k, ((e k).vec).1) - (∑ k, ((e k).vec).2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => ((rot_vec (e k)).2).symm
  rw [hsum1, hsum2]
  constructor
  · intro h
    have h' : ((∑ k, ((e k).vec).1), (∑ k, ((e k).vec).2)) = ((0 : ℤ), (0 : ℤ)) := by
      rw [← hfst, ← hsnd]; rw [h]; rfl
    exact (eq_zero_iff_rot _ _).mp h'
  · intro h
    have h' := (eq_zero_iff_rot (∑ k, ((e k).vec).1) (∑ k, ((e k).vec).2)).mpr h
    show (∑ k, (e k).vec) = (0 : ℤ × ℤ)
    rw [Prod.ext_iff]; rw [hfst, hsnd]
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

/-- The one dimensional return count at length `n`: the number of sign words
of length `n` summing to zero. -/
def oneDCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun u : Fin n → Bool => ∑ k, sgnVal (u k) = 0)).card

/-- **The planar return count is a square.** -/
theorem srwCount_eq_sq (n : ℕ) : srwCount n 0 = (oneDCount n) ^ 2 := by
  have hcard : srwCount n 0
      = (Finset.univ.filter (fun e : Fin n → Step => (∑ k, (e k).vec) = 0)).card := by
    rw [srwCount, Finset.card_filter]
    exact Finset.sum_congr rfl fun e _ => by simp
  rw [hcard]
  have hfilter : (Finset.univ.filter (fun e : Fin n → Step => (∑ k, (e k).vec) = 0)).card
      = (Finset.univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) =>
            (∑ k, sgnVal (p.1 k) = 0) ∧ (∑ k, sgnVal (p.2 k) = 0))).card := by
    apply Finset.card_bij (fun e _ => wordEquiv n e)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact (sum_vec_eq_zero_iff n e).mp he
    · intro a _ b _ hab
      exact (wordEquiv n).injective hab
    · intro p hp
      refine ⟨(wordEquiv n).symm p, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have := (sum_vec_eq_zero_iff n ((wordEquiv n).symm p)).mpr
      simpa using this (by simpa using hp)
  have hprod : (Finset.univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) =>
        (∑ k, sgnVal (p.1 k) = 0) ∧ (∑ k, sgnVal (p.2 k) = 0)))
      = (Finset.univ.filter (fun u : Fin n → Bool => ∑ k, sgnVal (u k) = 0)) ×ˢ
        (Finset.univ.filter (fun u : Fin n → Bool => ∑ k, sgnVal (u k) = 0)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hfilter, hprod, Finset.card_product, oneDCount, sq]

/-! ### The one dimensional return count is the central binomial coefficient -/

/-- A sign word sums to zero exactly when exactly half its entries are `+1`. -/
theorem sum_sgnVal_eq_zero_iff (m : ℕ) (u : Fin (2 * m) → Bool) :
    (∑ i, sgnVal (u i) = 0) ↔ (Finset.univ.filter (fun i => u i = true)).card = m := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * m)))) (p := fun i => u i = true)
  rw [Finset.card_fin] at hsplit
  have hsum : ∑ i, sgnVal (u i)
      = ((Finset.univ.filter (fun i => u i = true)).card : ℤ)
        - ((Finset.univ.filter (fun i => ¬ (u i = true))).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => u i = true)
      (fun i => sgnVal (u i))]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => u i = true), sgnVal (u i)
        = ((Finset.univ.filter (fun i => u i = true)).card : ℤ) := by
      calc ∑ i ∈ Finset.univ.filter (fun i => u i = true), sgnVal (u i)
          = ∑ _i ∈ Finset.univ.filter (fun i => u i = true), (1 : ℤ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have h : u i = true := (Finset.mem_filter.mp hi).2
            simp [sgnVal, h]
        _ = ((Finset.univ.filter (fun i => u i = true)).card : ℤ) := by simp
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ (u i = true)), sgnVal (u i)
        = - ((Finset.univ.filter (fun i => ¬ (u i = true))).card : ℤ) := by
      calc ∑ i ∈ Finset.univ.filter (fun i => ¬ (u i = true)), sgnVal (u i)
          = ∑ _i ∈ Finset.univ.filter (fun i => ¬ (u i = true)), (-1 : ℤ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have h : u i = false := by
              have hne := (Finset.mem_filter.mp hi).2
              cases hb : u i with
              | false => rfl
              | true => exact absurd hb hne
            simp [sgnVal, h]
        _ = - ((Finset.univ.filter (fun i => ¬ (u i = true))).card : ℤ) := by simp
    rw [h1, h2]; ring
  rw [hsum]
  omega

/-- **The one dimensional return count.** Among the `2 ^ (2m)` sign words of
length `2m`, exactly `C(2m, m)` sum to zero. -/
theorem oneDCount_two_mul (m : ℕ) : oneDCount (2 * m) = Nat.centralBinom m := by
  classical
  have hpc : ((Finset.univ : Finset (Fin (2 * m))).powersetCard m).card = (2 * m).choose m := by
    rw [Finset.card_powersetCard, Finset.card_fin]
  rw [oneDCount, Nat.centralBinom_eq_two_mul_choose, ← hpc]
  refine Finset.card_bij (fun u _ => Finset.univ.filter (fun k => u k = true)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (sum_sgnVal_eq_zero_iff m u).mp hu⟩
  · intro a _ b _ hab
    funext k
    have : (k ∈ Finset.univ.filter (fun i => a i = true))
        ↔ (k ∈ Finset.univ.filter (fun i => b i = true)) := Finset.ext_iff.mp hab k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases ha : a k <;> cases hb : b k <;> simp [ha, hb] at this ⊢
  · intro s hs
    refine ⟨fun k => decide (k ∈ s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine (sum_sgnVal_eq_zero_iff m _).mpr ?_
      have hcard := (Finset.mem_powersetCard.mp hs).2
      have : Finset.univ.filter (fun k => (decide (k ∈ s)) = true) = s := by
        ext k; simp
      rw [this]; exact hcard
    · ext k; simp

/-! ### A sharp lower bound on the central binomial coefficient

Mathlib has `Nat.four_pow_le_two_mul_self_mul_centralBinom`,
`4 ^ n ≤ 2 * n * centralBinom n`. That is a factor of `√n` weaker than what
recurrence of the two dimensional walk needs: it gives
`centralBinom n ^ 2 / 16 ^ n ≳ 1 / n ^ 2`, a convergent series, where the
truth is `≳ 1 / n`, a divergent one. The sharp form below is proved by
induction with exactly one unit of slack at each step, which is why the
weaker bound cannot be pushed to give it. -/

/-- The sharp central binomial lower bound `16 ^ n ≤ 4 n \binom{2n}{n}^2`. -/
theorem sixteen_pow_le (n : ℕ) (hn : 1 ≤ n) :
    16 ^ n ≤ 4 * n * (Nat.centralBinom n) ^ 2 := by
  induction n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ m ih =>
    cases m with
    | zero =>
      norm_num [Nat.centralBinom, Nat.choose]
    | succ k =>
      have squareStep : (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2
          = 4 * (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by
        have h := Nat.succ_mul_centralBinom_succ (k + 1)
        have hsq : ((k + 2) * Nat.centralBinom (k + 2)) ^ 2
            = (2 * (2 * k + 3) * Nat.centralBinom (k + 1)) ^ 2 := by
          rw [show k + 2 = k + 1 + 1 from rfl, h]
          ring_nf
        calc (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2
            = ((k + 2) * Nat.centralBinom (k + 2)) ^ 2 := by ring
          _ = (2 * (2 * k + 3) * Nat.centralBinom (k + 1)) ^ 2 := hsq
          _ = 4 * (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by ring
      have squareArith : 4 * (k + 1) * (k + 2) ≤ (2 * k + 3) ^ 2 := by
        have hExpand : (2 * k + 3) ^ 2 = 4 * (k + 1) * (k + 1) + 4 * (k + 1) + 1 := by ring
        calc 4 * (k + 1) * (k + 2)
            = 4 * (k + 1) * (k + 1) + 4 * (k + 1) := by ring
          _ ≤ 4 * (k + 1) * (k + 1) + 4 * (k + 1) + 1 := by omega
          _ = (2 * k + 3) ^ 2 := hExpand.symm
      have hIH := ih k.succ_pos
      have lowerBound : 16 ^ (k + 1) * (k + 2)
          ≤ (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by
        calc 16 ^ (k + 1) * (k + 2)
            ≤ 4 * (k + 1) * (Nat.centralBinom (k + 1)) ^ 2 * (k + 2) :=
              Nat.mul_le_mul_right (k + 2) hIH
          _ = 4 * (k + 1) * (k + 2) * (Nat.centralBinom (k + 1)) ^ 2 := by ring
          _ ≤ (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 :=
            Nat.mul_le_mul_right ((Nat.centralBinom (k + 1)) ^ 2) squareArith
      have scaled : 16 ^ (k + 1) * 16 * (k + 2)
          ≤ 4 * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2 := by
        calc 16 ^ (k + 1) * 16 * (k + 2)
            = 16 * (16 ^ (k + 1) * (k + 2)) := by ring
          _ ≤ 16 * ((2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2) :=
            Nat.mul_le_mul_left 16 lowerBound
          _ = 16 * (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by ring
          _ = 4 * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2 := by
            rw [show (4:ℕ) * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2
                  = 4 * ((k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2) from by ring,
                squareStep]
            ring
      have multiplied : (k + 2) * 16 ^ (k + 2)
          ≤ (k + 2) * (4 * (k + 2) * (Nat.centralBinom (k + 2)) ^ 2) := by
        calc (k + 2) * 16 ^ (k + 2)
            = (k + 2) * (16 ^ (k + 1) * 16) := by ring
          _ = 16 ^ (k + 1) * 16 * (k + 2) := by ring
          _ ≤ 4 * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2 := scaled
          _ = (k + 2) * (4 * (k + 2) * (Nat.centralBinom (k + 2)) ^ 2) := by ring
      exact Nat.le_of_mul_le_mul_left multiplied (by omega : 0 < k + 2)

/-- The sharp central binomial lower bound, restated as a real inequality
in the shape the return-probability estimate below uses. -/
theorem one_div_le_centralBinom_sq_div (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (4 * n) ≤ ((Nat.centralBinom n : ℝ)) ^ 2 / 16 ^ n := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [one_mul, mul_comm]
  exact_mod_cast sixteen_pow_le n hn

/-! ### Divergence of the harmonic series -/

/-- The scaled harmonic series diverges in `ℝ≥0∞`, where a divergent series is
simply equal to `⊤`. -/
theorem tsum_harmonic_eq_top :
    ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) = ⊤ := by
  have hcast : ∑' m : ℕ, ((1 / (4 * ((m : ℝ≥0) + 1)) : ℝ≥0) : ℝ≥0∞)
      = ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) := by
    refine tsum_congr fun m => ?_
    rw [ENNReal.coe_div (by positivity)]
    push_cast
    rfl
  rw [← hcast]
  by_contra hne
  have hsummable : Summable (fun m : ℕ => (1 / (4 * ((m : ℝ≥0) + 1)) : ℝ≥0)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hne
  have hreal : Summable (fun m : ℕ => ((1 / (4 * ((m : ℝ≥0) + 1)) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr hsummable
  have hshift : Summable (fun m : ℕ => (1 / ((m : ℝ) + 1))) := by
    have h4 := hreal.mul_left (4 : ℝ)
    refine h4.congr fun m => ?_
    push_cast
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    field_simp
  -- shifting the index by one contradicts divergence of the harmonic series
  have : Summable (fun n : ℕ => 1 / ((n : ℝ))) := by
    refine (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ))) 1).mp ?_
    refine hshift.congr fun m => ?_
    push_cast
    ring
  exact Real.not_summable_one_div_natCast this

/-! ### Assembling Pólya's theorem in two dimensions

The factor that decides recurrence versus transience is exactly the sharp
bound `sixteen_pow_le`: it makes the `m`-th even term of the Green series at
least `1 / (4 * m)`, and that series diverges. With Mathlib's own weaker
central binomial bound the terms would only be `≳ 1 / m ^ 2` and the sum
would converge. -/

/-- The even terms of the Green series dominate a multiple of the harmonic
series. -/
theorem harmonic_le_srwKernel
    (hcount : ∀ m : ℕ, oneDCount (2 * m) = Nat.centralBinom m) (m : ℕ) :
    (1 / (4 * (m + 1)) : ℝ≥0) ≤ srwKernel (2 * (m + 1)) := by
  have hsq : srwCount (2 * (m + 1)) 0 = (Nat.centralBinom (m + 1)) ^ 2 := by
    rw [srwCount_eq_sq, hcount (m + 1)]
  have hpow : ((4 : ℝ≥0))⁻¹ ^ (2 * (m + 1)) = ((16 : ℝ≥0))⁻¹ ^ (m + 1) := by
    rw [pow_mul]; norm_num
  rw [srwKernel, hsq, hpow]
  -- the integer bound `16 ^ (m+1) ≤ 4 * (m+1) * centralBinom (m+1) ^ 2`
  have hkey : (16 : ℝ≥0) ^ (m + 1)
      ≤ (4 * (m + 1) : ℝ≥0) * ((Nat.centralBinom (m + 1) : ℝ≥0)) ^ 2 := by
    have h := sixteen_pow_le (m + 1) (Nat.le_add_left 1 m)
    have := (Nat.cast_le (α := ℝ≥0)).mpr h
    push_cast at this
    convert this using 2
  have h16 : (0 : ℝ≥0) < 16 ^ (m + 1) := by positivity
  have hm : (0 : ℝ≥0) < 4 * (m + 1) := by positivity
  rw [div_le_iff₀ hm, inv_pow, ← div_eq_inv_mul, div_mul_eq_mul_div, le_div_iff₀ h16]
  calc (1 : ℝ≥0) * (16 : ℝ≥0) ^ (m + 1) = (16 : ℝ≥0) ^ (m + 1) := one_mul _
    _ ≤ (4 * (m + 1) : ℝ≥0) * ((Nat.centralBinom (m + 1) : ℝ≥0)) ^ 2 := hkey
    _ = (Nat.centralBinom (m + 1) : ℝ≥0) ^ 2 * (4 * (m + 1)) := mul_comm _ _
    _ = ((Nat.centralBinom (m + 1) ^ 2 : ℕ) : ℝ≥0) * (4 * (m + 1)) := by push_cast; rfl

/-- **Pólya's theorem in two dimensions**, given the one dimensional count and
the divergence of the harmonic series. -/
theorem simpleRandomWalkRecurrent_of
    (hcount : ∀ m : ℕ, oneDCount (2 * m) = Nat.centralBinom m)
    (hdiv : ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) = ⊤) :
    SimpleRandomWalkRecurrent := by
  have hinj : Function.Injective (fun m : ℕ => 2 * (m + 1)) := by
    intro a b hab; simpa using hab
  have hsub : ∑' m : ℕ, ((srwKernel (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      ≤ ∑' n : ℕ, ((srwKernel n : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj _
  have hterm : ∀ m : ℕ, ((1 / (4 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      ≤ ((srwKernel (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) := by
    intro m
    exact_mod_cast ENNReal.coe_le_coe.mpr (harmonic_le_srwKernel hcount m)
  have hlow : ∑' m : ℕ, ((1 / (4 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      ≤ ∑' m : ℕ, ((srwKernel (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.tsum_le_tsum hterm
  have hcast : ∑' m : ℕ, ((1 / (4 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      = ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) := by
    refine tsum_congr fun m => ?_
    rw [ENNReal.coe_div (by positivity)]
    push_cast
    rfl
  rw [hcast, hdiv] at hlow
  exact top_le_iff.mp (le_trans hlow hsub)

/-- The planar return count at even length, in closed form. -/
theorem srwCount_two_mul (m : ℕ) : srwCount (2 * m) 0 = (Nat.centralBinom m) ^ 2 := by
  rw [srwCount_eq_sq, oneDCount_two_mul]

/-- **Pólya's theorem in two dimensions.** The simple random walk on `ℤ²` is
recurrent: its Green series `∑ srwKernel n` diverges. -/
theorem simpleRandomWalkRecurrent : SimpleRandomWalkRecurrent :=
  simpleRandomWalkRecurrent_of oneDCount_two_mul tsum_harmonic_eq_top

end LatticeProb
