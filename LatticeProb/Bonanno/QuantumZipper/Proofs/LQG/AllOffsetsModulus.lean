/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AllOffsetsModulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (GaussTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# M4-B4, part 2: the modulus of the density in the offset (blueprint node B4a)

Blueprint `M4_BLUEPRINT.md`, node M4-B4 ("Modulus part", B4a).

At a fixed point `t` and scale `ε`, `d_{aε}(t) = d_{2ε}(t) · H(a)` with
`H(a) = (a/2)^{γ²/4} e^{(γ/2) Φ(a)}`, `Φ(a) = Z_{aε}(t) − Z_{2ε}(t)` independent of `Z_{2ε}(t)`.

* `chain_bound` (deterministic dyadic chaining on the points `dpt j l = 1 + l 2^{-j}` of
  `[1,2]`): `|h(a) − h(π_m a)| ≤ chainT m n h` for every level-`n` point `a`, where
  `chainT m n h = ∑_{m ≤ j < n} (θ^j + θ^{-3j} ∑_l (h(b_l) − h(π_j b_l))⁴)`, `θ = 7/8`.
* `bandH_moment`: `E (H(b) − H(b'))⁴ ≤ C (b − b')²` (the increment `Φ(b') − Φ(b)` is an
  independent Gaussian of variance `2 log(b/b')`; exact fourth moment of the tilt).
* `lintegral_dens_chainT_le`: `E[d_{2ε}(t) · chainT m n H] ≤ R^{γ²/4} C' θ^m`, uniformly in
  `n`, `ε`, `t`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist TwoRadius

/-! ## B1. Deterministic dyadic chaining -/

/-- The chaining ratio `θ = 7/8`. -/
def θm : ℝ := 7 / 8

theorem θm_pos : 0 < θm := by norm_num [θm]

theorem θm_lt_one : θm < 1 := by norm_num [θm]

/-- The dyadic point `1 + l 2^{-j}`. -/
def dpt (j l : ℕ) : ℝ := 1 + (l : ℝ) / 2 ^ j

/-- Fourth-power increments of `h` between level `j+1` and its level-`j` floor. -/
def incr (j : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (2 ^ (j + 1) + 1), (h (dpt (j + 1) l) - h (dpt j (l / 2))) ^ 4

/-- The chaining functional. -/
def chainT (m n : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico m n, (θm ^ j + incr j h / θm ^ (3 * j))

theorem incr_nonneg (j : ℕ) (h : ℝ → ℝ) : 0 ≤ incr j h :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem chainT_nonneg (m n : ℕ) (h : ℝ → ℝ) : 0 ≤ chainT m n h :=
  Finset.sum_nonneg fun j _ =>
    add_nonneg (pow_pos θm_pos j).le (div_nonneg (incr_nonneg j h) (pow_pos θm_pos _).le)

theorem abs_le_add_pow4 (x : ℝ) {lam : ℝ} (hl : 0 < lam) : |x| ≤ lam + x ^ 4 / lam ^ 3 := by
  rcases le_or_gt |x| lam with h | h
  · have : 0 ≤ x ^ 4 / lam ^ 3 := by positivity
    linarith
  · have hx4 : x ^ 4 = |x| ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    have h3 : lam ^ 3 ≤ |x| ^ 3 := pow_le_pow_left₀ hl.le h.le 3
    have : |x| ≤ x ^ 4 / lam ^ 3 := by
      rw [le_div_iff₀ (by positivity), hx4]
      calc |x| * lam ^ 3 ≤ |x| * |x| ^ 3 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |x| ^ 4 := by ring
    linarith

theorem term_le_incr (j : ℕ) (h : ℝ → ℝ) {l : ℕ} (hl : l ≤ 2 ^ (j + 1)) :
    (h (dpt (j + 1) l) - h (dpt j (l / 2))) ^ 4 ≤ incr j h :=
  Finset.single_le_sum (f := fun l => (h (dpt (j + 1) l) - h (dpt j (l / 2))) ^ 4)
    (fun _ _ => by positivity) (Finset.mem_range.2 (by omega))

/-- **Dyadic chaining.** -/
theorem chain_bound (h : ℝ → ℝ) (m : ℕ) : ∀ d : ℕ, ∀ i ≤ 2 ^ (m + d),
    |h (dpt (m + d) i) - h (dpt m (i / 2 ^ d))| ≤ chainT m (m + d) h := by
  intro d
  induction d with
  | zero => intro i _; simp [chainT]
  | succ d ih =>
    intro i hi
    have hmd : m + (d + 1) = m + d + 1 := by omega
    rw [hmd] at hi ⊢
    have hi2 : i / 2 ≤ 2 ^ (m + d) := Nat.div_le_of_le_mul (by rw [pow_succ] at hi; linarith)
    have e1 : i / 2 ^ (d + 1) = i / 2 / 2 ^ d := by rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [e1]
    have hsplit : chainT m (m + d + 1) h =
        chainT m (m + d) h + (θm ^ (m + d) + incr (m + d) h / θm ^ (3 * (m + d))) :=
      Finset.sum_Ico_succ_top (by omega) _
    rw [hsplit]
    have hθ := pow_pos θm_pos (m + d)
    have hterm := abs_le_add_pow4 (h (dpt (m + d + 1) i) - h (dpt (m + d) (i / 2))) hθ
    have hinc := term_le_incr (m + d) h hi
    have hp : (θm ^ (m + d)) ^ 3 = θm ^ (3 * (m + d)) := by rw [← pow_mul, mul_comm]
    rw [hp] at hterm
    have hterm' : |h (dpt (m + d + 1) i) - h (dpt (m + d) (i / 2))| ≤
        θm ^ (m + d) + incr (m + d) h / θm ^ (3 * (m + d)) :=
      hterm.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hinc (pow_pos θm_pos _).le))
    calc _ ≤ |h (dpt (m + d + 1) i) - h (dpt (m + d) (i / 2))| +
          |h (dpt (m + d) (i / 2)) - h (dpt m (i / 2 / 2 ^ d))| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [ih (i / 2) hi2]

theorem chainT_congr (m n : ℕ) {h h' : ℝ → ℝ}
    (hh : ∀ j l : ℕ, l ≤ 2 ^ j → h (dpt j l) = h' (dpt j l)) : chainT m n h = chainT m n h' := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [hh (j + 1) l (by omega), hh j (l / 2) (Nat.div_le_of_le_mul (by rw [pow_succ] at hl'; omega))]

theorem dpt_ge_one (j l : ℕ) : 1 ≤ dpt j l := by
  unfold dpt; have : (0 : ℝ) ≤ l / 2 ^ j := by positivity
  linarith

theorem dpt_le_two {j l : ℕ} (hl : l ≤ 2 ^ j) : dpt j l ≤ 2 := by
  unfold dpt
  have : (l : ℝ) / 2 ^ j ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hl
  linarith

theorem dpt_diff (j l : ℕ) : dpt (j + 1) l - dpt j (l / 2) = ((l % 2 : ℕ) : ℝ) / 2 ^ (j + 1) := by
  have hl : (l : ℝ) = 2 * ((l / 2 : ℕ) : ℝ) + ((l % 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod l 2).symm
  unfold dpt
  rw [hl]
  field_simp
  ring

theorem dpt_diff_nonneg (j l : ℕ) : 0 ≤ dpt (j + 1) l - dpt j (l / 2) := by
  rw [dpt_diff]; positivity

theorem dpt_diff_le (j l : ℕ) : dpt (j + 1) l - dpt j (l / 2) ≤ 1 / 2 ^ (j + 1) := by
  rw [dpt_diff]
  have : ((l % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt l two_pos)
  exact div_le_div_of_nonneg_right this (by positivity)

/-! ## B2. Gaussian moments of the tilt -/

theorem integral_exp_n_tilt (γ : ℝ) (w : ℝ≥0) (n : ℝ) :
    Integrable (fun d => exp (n * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) (gaussianReal 0 w) ∧
    ∫ d, exp (n * (-(γ ^ 2 / 8 * w) + γ / 2 * d)) ∂gaussianReal 0 w =
      exp (n * (n - 1) * (γ ^ 2 / 8 * w)) := by
  have e : (fun d : ℝ => exp (n * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) =
      fun d => exp (n * (-(γ ^ 2 / 8 * w)) + n * (γ / 2) * d) := by
    funext d; congr 1; ring
  rw [e]
  refine ⟨integrable_exp_mul_add_gaussianReal w _ _, ?_⟩
  rw [integral_exp_mul_add_gaussianReal]
  congr 1; ring

theorem tiltY_pow4_eq (γ w d : ℝ) :
    tiltY γ w d ^ 4 = 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      - 4 * exp (3 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + exp (4 * (-(γ ^ 2 / 8 * w) + γ / 2 * d)) := by
  unfold tiltY
  have h2 : ∀ A : ℝ, exp (2 * A) = exp A ^ 2 := fun A => by rw [← exp_nat_mul]; norm_num
  have h3 : ∀ A : ℝ, exp (3 * A) = exp A ^ 3 := fun A => by rw [← exp_nat_mul]; norm_num
  have h4 : ∀ A : ℝ, exp (4 * A) = exp A ^ 4 := fun A => by rw [← exp_nat_mul]; norm_num
  rw [h2, h3, h4, one_mul]
  ring

theorem tiltY_pow4_moment (γ : ℝ) (w : ℝ≥0) :
    Integrable (fun d => tiltY γ w d ^ 4) (gaussianReal 0 w) ∧
    ∫ d, tiltY γ w d ^ 4 ∂gaussianReal 0 w =
      6 * exp (2 * (γ ^ 2 / 8 * w)) - 4 * exp (6 * (γ ^ 2 / 8 * w)) +
        exp (12 * (γ ^ 2 / 8 * w)) - 3 := by
  have hE := fun n : ℝ => integral_exp_n_tilt γ w n
  have e : (fun d => tiltY γ w d ^ 4) = fun d =>
      1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      - 4 * exp (3 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + exp (4 * (-(γ ^ 2 / 8 * w) + γ / 2 * d)) := funext fun d => tiltY_pow4_eq γ w d
  rw [e]
  have i0 : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 w) := integrable_const _
  have i1 := (hE 1).1.const_mul 4
  have i2 := (hE 2).1.const_mul 6
  have i3 := (hE 3).1.const_mul 4
  have i4 := (hE 4).1
  have j1 : Integrable (fun d : ℝ => 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d)))
      (gaussianReal 0 w) := i0.sub i1
  have j2 : Integrable (fun d : ℝ => 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) (gaussianReal 0 w) := j1.add i2
  have j3 : Integrable (fun d : ℝ => 1 - 4 * exp (1 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      + 6 * exp (2 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))
      - 4 * exp (3 * (-(γ ^ 2 / 8 * w) + γ / 2 * d))) (gaussianReal 0 w) := j2.sub i3
  refine ⟨j3.add i4, ?_⟩
  rw [integral_add j3 i4, integral_sub j2 i3,
    integral_add j1 i2, integral_sub i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, (hE 1).2, (hE 2).2, (hE 3).2, (hE 4).2, integral_const]
  have e1 : exp (1 * (1 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = 1 := by simp
  have e2 : exp (2 * (2 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = exp (2 * (γ ^ 2 / 8 * w)) := by
    congr 1; ring
  have e3 : exp (3 * (3 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = exp (6 * (γ ^ 2 / 8 * w)) := by
    congr 1; ring
  have e4 : exp (4 * (4 - 1) * (γ ^ 2 / 8 * (w : ℝ))) = exp (12 * (γ ^ 2 / 8 * w)) := by
    congr 1; ring
  rw [e1, e2, e3, e4]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-! ## B3. The band process at a fixed point -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem sum_Ico_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m n : ℕ) :
    ∑ j ∈ Finset.Ico m n, q ^ j ≤ q ^ m / (1 - q) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hq0 hq1 _) (pow_nonneg hq0 _)

theorem ratio_eq (j : ℕ) : 1 / 2 ^ j / θm ^ (3 * j) = (256 / 343 : ℝ) ^ j := by
  have h : (2 : ℝ) * θm ^ 3 = 343 / 256 := by norm_num [θm]
  rw [pow_mul, div_div, ← mul_pow, h, one_div, ← inv_pow]
  norm_num

/-! ## B4. The density modulus at the level of the regularized field -/

end AllOffsets
end QuantumZipper
