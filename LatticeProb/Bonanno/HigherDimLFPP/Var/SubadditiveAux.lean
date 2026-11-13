/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.SubadditiveAux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Basic
import Mathlib.Tactic.Module

/-!
# The coarse/fine decomposition behind (2.6)

For `f ∈ Vg E (n + r)`, let `g = coarse n f ∈ Vg E n` be the interpolant of `f` at the coarse
vertices `k 2⁻ⁿ`, and `fine n f k ∈ Vg E r` the rescaled fine pieces
`t ↦ 2ⁿ (f - g)((k + t) 2⁻ⁿ)` (`k < 2ⁿ`).  Then (HA1 D5):

* `decomp_piece`: `f = g + 2⁻ⁿ (fine n f k)(2ⁿ x - k)` on the `k`-th coarse interval;
* `energy_decomp`: `E(f) = E(g) + ∑ₖ 2⁻ⁿ E(fine n f k)` (the cross term vanishes; the vector form
  `block_identity` uses the inner product);
* `l1_decomp`: `∫₀¹ ‖f - f'‖ ≤ ∫₀¹ ‖g - g'‖ + ∑ₖ 2⁻²ⁿ ∫₀¹ ‖fine n f k - fine n f' k‖`.

Ported from `LQGDimension/Section2/SubadditiveAux.lean` (sections "The coarse interpolant" to
"`L¹` decomposition"), with `16 → 2` and scalar → `E`-valued profiles.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The coarse interpolant -/

/-- Linear interpolation of `f` on the mesh `2⁻ⁿ`: with `k = ⌊2ⁿ x⌋` and `t = 2ⁿ x - k`, it is
`(1 - t) f(k 2⁻ⁿ) + t f((k+1) 2⁻ⁿ)`. -/
def coarse (n : ℕ) (f : ℝ → E) (x : ℝ) : E :=
  (1 - ((2 : ℝ) ^ n * x - ((⌊(2 : ℝ) ^ n * x⌋ : ℤ) : ℝ))) •
      f (((⌊(2 : ℝ) ^ n * x⌋ : ℤ) : ℝ) / 2 ^ n) +
    ((2 : ℝ) ^ n * x - ((⌊(2 : ℝ) ^ n * x⌋ : ℤ) : ℝ)) •
      f ((((⌊(2 : ℝ) ^ n * x⌋ : ℤ) : ℝ) + 1) / 2 ^ n)

lemma coarse_piece (n : ℕ) (f : ℝ → E) (k : ℤ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)) :
    coarse n f x = (1 - (2 ^ n * x - k)) • f ((k : ℝ) / 2 ^ n) +
      (2 ^ n * x - k) • f (((k : ℝ) + 1) / 2 ^ n) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : (k : ℝ) ≤ 2 ^ n * x := by
    have := hx.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : 2 ^ n * x ≤ (k : ℝ) + 1 := by
    have := hx.2; rw [le_div_iff₀ hN] at this; linarith
  rcases h2.lt_or_eq with h2 | h2
  · have hfl : ⌊(2 : ℝ) ^ n * x⌋ = k := Int.floor_eq_iff.2 ⟨h1, h2⟩
    rw [coarse, hfl]
  · have hfl : ⌊(2 : ℝ) ^ n * x⌋ = k + 1 := by
      rw [h2]; exact_mod_cast Int.floor_intCast (k + 1)
    rw [coarse, hfl, h2]
    push_cast
    simp

lemma coarse_piece_nat (n : ℕ) (f : ℝ → E) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)) :
    coarse n f x = (1 - (2 ^ n * x - k)) • f ((k : ℝ) / 2 ^ n) +
      (2 ^ n * x - k) • f (((k : ℝ) + 1) / 2 ^ n) := by
  have := coarse_piece n f (k : ℤ) (x := x) (by simpa using hx)
  simpa using this

lemma coarse_node (n : ℕ) (f : ℝ → E) (y : ℝ) (hy : ∃ j : ℤ, (j : ℝ) = y) :
    coarse n f (y / 2 ^ n) = f (y / 2 ^ n) := by
  obtain ⟨j, rfl⟩ := hy
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have e : (2 : ℝ) ^ n * ((j : ℝ) / 2 ^ n) = j := by field_simp
  rw [coarse, e, Int.floor_intCast]
  simp

omit [NormedSpace ℝ E] in
lemma zero_of_le_of_zero {f : ℝ → E} (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hout : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) : f x = 0 := by
  by_cases hx' : x ∈ Icc (0 : ℝ) 1
  · rcases hx with hx | hx
    · rw [le_antisymm hx hx'.1]; exact h0
    · rw [le_antisymm hx'.2 hx]; exact h1
  · exact hout x hx'

lemma coarse_mem (n : ℕ) {f : ℝ → E} (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hout : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) : coarse n f ∈ Vg E n := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hz := fun x hx => zero_of_le_of_zero h0 h1 hout (x := x) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := coarse_node n f 0 ⟨0, by simp⟩
    simpa [h0] using this
  · have := coarse_node n f (2 ^ n) ⟨2 ^ n, by push_cast; ring⟩
    rw [div_self hN.ne'] at this
    rw [this, h1]
  · intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    have hk : ∀ k : ℤ, k = ⌊(2 : ℝ) ^ n * x⌋ →
        f ((k : ℝ) / 2 ^ n) = 0 ∧ f (((k : ℝ) + 1) / 2 ^ n) = 0 := by
      intro k hk
      rcases hx with hx | hx
      · have hk0 : k < 0 := by
          rw [hk, Int.floor_lt]; push_cast; nlinarith
        have hk1 : (k : ℝ) + 1 ≤ 0 := by
          have : k + 1 ≤ 0 := by omega
          exact_mod_cast this
        constructor
        · apply hz; left; rw [div_le_iff₀ hN]; linarith
        · apply hz; left; rw [div_le_iff₀ hN]; linarith
      · have hk0 : (2 : ℤ) ^ n ≤ k := by
          rw [hk, Int.le_floor]; push_cast; nlinarith
        have hk0' : (2 : ℝ) ^ n ≤ k := by exact_mod_cast hk0
        constructor
        · apply hz; right; rw [le_div_iff₀ hN]; linarith
        · apply hz; right; rw [le_div_iff₀ hN]; linarith
    obtain ⟨e1, e2⟩ := hk _ rfl
    rw [coarse, e1, e2]
    simp
  · intro k hk
    refine ⟨(2 : ℝ) ^ n • (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)),
      f ((k : ℝ) / 2 ^ n) - (k : ℝ) • (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)),
      fun x hx => ?_⟩
    rw [coarse_piece_nat n f k hx]
    module

/-! ## The rescaled fine pieces -/

/-- The fine part `f - coarse n f` on the `k`-th coarse interval, rescaled to `[0,1]`:
`t ↦ 2ⁿ (f - g)((k + t) 2⁻ⁿ)` for `t ∈ [0,1]`, and `0` otherwise. -/
def fine (n : ℕ) (f : ℝ → E) (k : ℕ) (t : ℝ) : E :=
  if t ∈ Icc (0 : ℝ) 1 then
    (2 : ℝ) ^ n • (f (((k : ℝ) + t) / 2 ^ n) -
      ((1 - t) • f ((k : ℝ) / 2 ^ n) + t • f (((k : ℝ) + 1) / 2 ^ n)))
  else 0

lemma fine_mem {n m : ℕ} {f : ℝ → E} (hf : f ∈ Vg E (n + m)) {k : ℕ} (hk : k < 2 ^ n) :
    fine n f k ∈ Vg E m := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [fine]
  · simp [fine]
  · intro x hx; simp [fine, hx]
  · intro i hi
    have hj : k * 2 ^ m + i < 2 ^ (n + m) := by
      rw [pow_add]
      have : k + 1 ≤ 2 ^ n := hk
      nlinarith
    have hjc : (((k * 2 ^ m + i : ℕ) : ℝ)) = (k : ℝ) * 2 ^ m + i := by push_cast; ring
    set j : ℕ := k * 2 ^ m + i with hjdef
    set D : E := f (((j : ℝ) + 1) / 2 ^ (n + m)) - f ((j : ℝ) / 2 ^ (n + m)) with hD
    refine ⟨(2 : ℝ) ^ n • ((2 : ℝ) ^ m • D + f ((k : ℝ) / 2 ^ n) - f (((k : ℝ) + 1) / 2 ^ n)),
      (2 : ℝ) ^ n • (f ((j : ℝ) / 2 ^ (n + m)) - (i : ℝ) • D - f ((k : ℝ) / 2 ^ n)),
      fun t ht => ?_⟩
    have ht1 : (i : ℝ) ≤ t * 2 ^ m := by
      have := ht.1; rwa [div_le_iff₀ hM] at this
    have ht2 : t * 2 ^ m ≤ (i : ℝ) + 1 := by
      have := ht.2; rwa [le_div_iff₀ hM] at this
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        nlinarith
      · have hi' : (i : ℝ) + 1 ≤ 2 ^ m := by
          have : i + 1 ≤ 2 ^ m := hi
          exact_mod_cast this
        nlinarith
    have hy : ((k : ℝ) + t) / 2 ^ n ∈ Icc ((j : ℝ) / 2 ^ (n + m))
        (((j : ℝ) + 1) / 2 ^ (n + m)) := by
      rw [hjc, pow_add]
      constructor
      · rw [div_le_div_iff₀ (by positivity) hN]
        nlinarith [mul_le_mul_of_nonneg_left ht1 hN.le]
      · rw [div_le_div_iff₀ hN (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left ht2 hN.le]
    rw [fine, ite_eq_left ht01, Vg_piece hf hj hy]
    have e : (2 : ℝ) ^ (n + m) * (((k : ℝ) + t) / 2 ^ n) - (j : ℝ) = 2 ^ m * t - i := by
      rw [hjc, pow_add]; field_simp; ring
    rw [e, ← hD]
    module

lemma fine_node (n m : ℕ) (f : ℝ → E) (k : ℕ) {i : ℕ} (hi : i ≤ 2 ^ m) :
    fine n f k ((i : ℝ) / 2 ^ m) = (2 : ℝ) ^ n • (f (((k * 2 ^ m + i : ℕ) : ℝ) / 2 ^ (n + m)) -
      ((1 - (i : ℝ) / 2 ^ m) • f ((k : ℝ) / 2 ^ n) +
        ((i : ℝ) / 2 ^ m) • f (((k : ℝ) + 1) / 2 ^ n))) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hi' : (i : ℝ) ≤ 2 ^ m := by exact_mod_cast hi
  have h01 : (i : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hM]; exact hi'
  have e : ((k : ℝ) + (i : ℝ) / 2 ^ m) / 2 ^ n =
      ((k * 2 ^ m + i : ℕ) : ℝ) / 2 ^ (n + m) := by
    push_cast; rw [pow_add]; field_simp
  rw [fine, ite_eq_left h01, e]

/-- On the `k`-th coarse interval, `f = g + 2⁻ⁿ fine n f k (2ⁿ x - k)`. -/
lemma decomp_piece (n : ℕ) (f : ℝ → E) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)) :
    f x = coarse n f x + (1 / (2 : ℝ) ^ n) • fine n f k (2 ^ n * x - k) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : (k : ℝ) ≤ 2 ^ n * x := by
    have := hx.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : 2 ^ n * x ≤ (k : ℝ) + 1 := by
    have := hx.2; rw [le_div_iff₀ hN] at this; linarith
  have ht : 2 ^ n * x - k ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have e : ((k : ℝ) + (2 ^ n * x - k)) / 2 ^ n = x := by field_simp; ring
  rw [coarse_piece_nat n f k hx, fine, ite_eq_left ht, e, smul_smul, one_div,
    inv_mul_cancel₀ hN.ne', one_smul]
  abel

lemma coarse_continuous {n p : ℕ} {f : ℝ → E} (hf : f ∈ Vg E p) : Continuous (coarse n f) :=
  Vg_continuous (coarse_mem n hf.1 hf.2.1 hf.2.2.1)

/-! ## `L¹` decomposition -/

lemma l1_decomp {n m : ℕ} {f f' : ℝ → E} (hf : f ∈ Vg E (n + m)) (hf' : f' ∈ Vg E (n + m)) :
    ∫ x in (0 : ℝ)..1, ‖f x - f' x‖ ≤ (∫ x in (0 : ℝ)..1, ‖coarse n f x - coarse n f' x‖) +
      ∑ k ∈ Finset.range (2 ^ n),
        (1 / (2 : ℝ) ^ n) ^ 2 * ∫ t in (0 : ℝ)..1, ‖fine n f k t - fine n f' k t‖ := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hfc := Vg_continuous hf
  have hfc' := Vg_continuous hf'
  have hgc := coarse_continuous (n := n) hf
  have hgc' := coarse_continuous (n := n) hf'
  set a : ℕ → ℝ := fun k => (k : ℝ) / 2 ^ n with ha
  have h0 : a 0 = 0 := by simp [ha]
  have h1 : a (2 ^ n) = 1 := by simp [ha, hN.ne']
  have hle : ∀ k, a k ≤ a (k + 1) := by
    intro k; simp only [ha]; gcongr; linarith
  have split1 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a)
    (n := 2 ^ n) (f := fun x => ‖f x - f' x‖)
    (fun k _ => ((hfc.sub hfc').norm).intervalIntegrable _ _)
  have split2 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a)
    (n := 2 ^ n) (f := fun x => ‖coarse n f x - coarse n f' x‖)
    (fun k _ => ((hgc.sub hgc').norm).intervalIntegrable _ _)
  rw [h0, h1] at split1 split2
  rw [← split1, ← split2, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have huc := Vg_continuous (fine_mem hf hk')
  have huc' := Vg_continuous (fine_mem hf' hk')
  have hcomp : Continuous fun x : ℝ =>
      ‖fine n f k (2 ^ n * x - k) - fine n f' k (2 ^ n * x - k)‖ := by
    fun_prop
  calc ∫ x in a k..a (k + 1), ‖f x - f' x‖
      ≤ ∫ x in a k..a (k + 1), (‖coarse n f x - coarse n f' x‖ +
          (1 / (2 : ℝ) ^ n) * ‖fine n f k (2 ^ n * x - k) - fine n f' k (2 ^ n * x - k)‖) := by
        refine intervalIntegral.integral_mono_on (hle k)
          (((hfc.sub hfc').norm).intervalIntegrable _ _)
          ((((hgc.sub hgc').norm).add (continuous_const.mul hcomp)).intervalIntegrable _ _)
          fun x hx => ?_
        have hx' : x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n) := by
          simpa [ha] using hx
        rw [decomp_piece n f k hx', decomp_piece n f' k hx']
        have e : coarse n f x + (1 / (2 : ℝ) ^ n) • fine n f k (2 ^ n * x - k) -
            (coarse n f' x + (1 / (2 : ℝ) ^ n) • fine n f' k (2 ^ n * x - k)) =
            (coarse n f x - coarse n f' x) +
              (1 / (2 : ℝ) ^ n) • (fine n f k (2 ^ n * x - k) - fine n f' k (2 ^ n * x - k)) := by
          rw [smul_sub]; abel
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ n)]
    _ = (∫ x in a k..a (k + 1), ‖coarse n f x - coarse n f' x‖) +
          (1 / (2 : ℝ) ^ n) ^ 2 * ∫ t in (0 : ℝ)..1, ‖fine n f k t - fine n f' k t‖ := by
        have i1 : IntervalIntegrable (fun x => ‖coarse n f x - coarse n f' x‖) volume
            (a k) (a (k + 1)) := ((hgc.sub hgc').norm).intervalIntegrable _ _
        have i2 : IntervalIntegrable (fun x => 1 / (2 : ℝ) ^ n *
            ‖fine n f k (2 ^ n * x - k) - fine n f' k (2 ^ n * x - k)‖) volume
            (a k) (a (k + 1)) := (continuous_const.mul hcomp).intervalIntegrable _ _
        rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul]
        have hsub := intervalIntegral.integral_comp_mul_sub (a := a k) (b := a (k + 1))
          (fun t => ‖fine n f k t - fine n f' k t‖) hN.ne' (k : ℝ)
        rw [hsub]
        have e1 : (2 : ℝ) ^ n * a k - k = 0 := by simp only [ha]; field_simp; ring
        have e2 : (2 : ℝ) ^ n * a (k + 1) - k = 1 := by
          simp only [ha]; push_cast; field_simp; ring
        rw [e1, e2, smul_eq_mul]
        ring

end Normed

/-! ## Energy decomposition -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sum_range_mul_split (N M : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N * M), h j =
      ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range M, h (k * M + i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The algebraic identity behind `E(f) = E(g) + E(u)` on one coarse interval (vector form: the
cross term `⟪∑ᵢ δᵢ, D⟫ = ‖D‖²` uses the inner product). -/
lemma block_identity (A U : ℕ → E) (M : ℕ) (hM : 0 < M) (N L Mr : ℝ) (hN : 0 < N)
    (hMr : Mr = M) (hL : L = N * Mr)
    (hU : ∀ i ≤ M, U i = N • (A i - ((1 - (i : ℝ) / Mr) • A 0 + ((i : ℝ) / Mr) • A M))) :
    L / 2 * ∑ i ∈ Finset.range M, ‖A (i + 1) - A i‖ ^ 2 =
      N / 2 * ‖A M - A 0‖ ^ 2 +
        1 / N * (Mr / 2 * ∑ i ∈ Finset.range M, ‖U (i + 1) - U i‖ ^ 2) := by
  subst hL hMr
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set D := A M - A 0 with hD
  have key : ∀ i ∈ Finset.range M, ‖U (i + 1) - U i‖ ^ 2 =
      N ^ 2 * ‖A (i + 1) - A i‖ ^ 2 - (2 * N ^ 2 / M) * ⟪A (i + 1) - A i, D⟫ +
        N ^ 2 * ‖D‖ ^ 2 / M ^ 2 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hdiff : U (i + 1) - U i = N • ((A (i + 1) - A i) - (1 / (M : ℝ)) • D) := by
      rw [hU (i + 1) hi', hU i hi'.le, hD]
      push_cast
      module
    rw [hdiff, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real, norm_smul,
      inner_smul_right, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / M)]
    field_simp
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← sum_inner, Finset.sum_range_sub A M, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← hD, real_inner_self_eq_norm_sq]
  field_simp
  ring

lemma energy_decomp {n m : ℕ} {f : ℝ → E} (hf : f ∈ Vg E (n + m)) :
    energy f = energy (coarse n f) +
      ∑ k ∈ Finset.range (2 ^ n), (1 / (2 : ℝ) ^ n) * energy (fine n f k) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hg := coarse_mem n hf.1 hf.2.1 hf.2.2.1
  have hsplit : energy f = ∑ k ∈ Finset.range (2 ^ n), (2 : ℝ) ^ (n + m) / 2 *
      ∑ i ∈ Finset.range (2 ^ m), ‖f ((((k * 2 ^ m + i : ℕ) : ℝ) + 1) / 2 ^ (n + m)) -
        f (((k * 2 ^ m + i : ℕ) : ℝ) / 2 ^ (n + m))‖ ^ 2 := by
    rw [Vg_energy hf, ← Finset.mul_sum,
      show (2 : ℕ) ^ (n + m) = 2 ^ n * 2 ^ m from pow_add 2 n m, sum_range_mul_split]
  rw [hsplit, Vg_energy hg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Vg_energy (fine_mem hf (Finset.mem_range.1 hk)),
    coarse_node n f ((k : ℝ) + 1) ⟨k + 1, by simp⟩, coarse_node n f (k : ℝ) ⟨k, by simp⟩]
  set A : ℕ → E := fun i => f (((k * 2 ^ m + i : ℕ) : ℝ) / 2 ^ (n + m)) with hA
  set U : ℕ → E := fun i => fine n f k ((i : ℝ) / 2 ^ m) with hU
  have hA0 : A 0 = f ((k : ℝ) / 2 ^ n) := by
    simp only [hA]; congr 1
    rw [pow_add, div_eq_div_iff (by positivity) (by positivity)]; push_cast; ring
  have hAM : A (2 ^ m) = f (((k : ℝ) + 1) / 2 ^ n) := by
    simp only [hA]; congr 1
    rw [pow_add, div_eq_div_iff (by positivity) (by positivity)]; push_cast; ring
  have hF1 : ∀ i : ℕ, f ((((k * 2 ^ m + i : ℕ) : ℝ) + 1) / 2 ^ (n + m)) = A (i + 1) := by
    intro i; simp only [hA]; congr 2; push_cast; ring
  have hF2 : ∀ i : ℕ, fine n f k (((i : ℝ) + 1) / 2 ^ m) = U (i + 1) := by
    intro i; simp only [hU]; push_cast; rfl
  have hUA : ∀ i ≤ 2 ^ m, U i =
      (2 : ℝ) ^ n • (A i - ((1 - (i : ℝ) / 2 ^ m) • A 0 + ((i : ℝ) / 2 ^ m) • A (2 ^ m))) := by
    intro i hi
    rw [hA0, hAM]
    exact fine_node n m f k hi
  simp only [hF1, hF2]
  rw [← hA0, ← hAM]
  exact block_identity A U (2 ^ m) (by positivity) (2 ^ n) ((2 : ℝ) ^ (n + m)) (2 ^ m) hN
    (by push_cast; ring) (pow_add 2 n m) hUA

end Inner

end HigherDimLFPP.Var
