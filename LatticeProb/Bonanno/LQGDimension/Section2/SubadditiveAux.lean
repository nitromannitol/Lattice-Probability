/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.SubadditiveAux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Section2

/-!
# Auxiliary lemmas for the subadditivity `a_{n+m} ≤ a_n + a_m`

Piecewise-linear functions of `V p`: affine formula on mesh intervals, continuity, the discrete
formula for the energy, and the decomposition `f = g + u` of `f ∈ V (n+m)` into its coarse
interpolant `g ∈ V n` and rescaled fine pieces in `V m`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.Subadd

/-! ## Functions of `V p` -/

lemma V_piece {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) {k : ℕ} (hk : k < 16 ^ p) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 16 ^ p) (((k : ℝ) + 1) / 16 ^ p)) :
    f x = f ((k : ℝ) / 16 ^ p) + (16 ^ p * x - k) *
      (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p)) := by
  obtain ⟨α, β, h⟩ := hf.2.2.2 k hk
  have hL : (0 : ℝ) < 16 ^ p := by positivity
  have hle : (k : ℝ) / 16 ^ p ≤ ((k : ℝ) + 1) / 16 ^ p := by gcongr; linarith
  rw [h x hx, h _ (left_mem_Icc.2 hle), h _ (right_mem_Icc.2 hle)]
  field_simp
  ring

lemma V_zero_of_le {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    f x = 0 := by
  by_cases hx' : x ∈ Icc (0 : ℝ) 1
  · rcases hx with hx | hx
    · rw [le_antisymm hx hx'.1]; exact hf.1
    · rw [le_antisymm hx'.2 hx]; exact hf.2.1
  · exact hf.2.2.1 x hx'

lemma V_continuousOn_Icc {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) :
    ∀ j : ℕ, j ≤ 16 ^ p → ContinuousOn f (Icc 0 ((j : ℝ) / 16 ^ p)) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 : (0 : ℝ) ≤ (j : ℝ) / 16 ^ p := by positivity
    have h2 : (j : ℝ) / 16 ^ p ≤ ((j : ℝ) + 1) / 16 ^ p := by gcongr; linarith
    rw [Nat.cast_succ, ← Icc_union_Icc_eq_Icc h1 h2]
    refine (ih (by omega)).union_of_isClosed ?_ isClosed_Icc isClosed_Icc
    obtain ⟨α, β, h⟩ := hf.2.2.2 j (by omega)
    exact ((continuous_const.mul continuous_id).add continuous_const).continuousOn.congr
      (fun x hx => h x hx)

lemma V_continuous {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) : Continuous f := by
  have hL : (0 : ℝ) < 16 ^ p := by positivity
  have h01 : ContinuousOn f (Icc 0 1) := by
    have := V_continuousOn_Icc hf (16 ^ p) le_rfl
    rwa [Nat.cast_pow, Nat.cast_ofNat, div_self hL.ne'] at this
  have hL0 : ContinuousOn f (Iic 0) :=
    continuousOn_const.congr (fun x hx => V_zero_of_le hf (Or.inl hx))
  have hR0 : ContinuousOn f (Ici 1) :=
    continuousOn_const.congr (fun x hx => V_zero_of_le hf (Or.inr hx))
  have := (hL0.union_of_isClosed h01 isClosed_Iic isClosed_Icc).union_of_isClosed hR0
    (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  rw [Iic_union_Icc_eq_Iic zero_le_one, Iic_union_Ici] at this
  exact continuousOn_univ.1 this

lemma V_hasDerivAt {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) {k : ℕ} (hk : k < 16 ^ p) {x : ℝ}
    (hx : x ∈ Ioo ((k : ℝ) / 16 ^ p) (((k : ℝ) + 1) / 16 ^ p)) :
    HasDerivAt f (16 ^ p * (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p))) x := by
  have hev : f =ᶠ[𝓝 x] fun y => f ((k : ℝ) / 16 ^ p) + (16 ^ p * y - k) *
      (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p)) := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    exact V_piece hf hk hy
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have := ((((hasDerivAt_id x).const_mul ((16 : ℝ) ^ p)).sub_const (k : ℝ)).mul_const
    (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p))).const_add (f ((k : ℝ) / 16 ^ p))
  convert this using 1 <;> simp

/-- The discrete formula for the energy of `f ∈ V p`. -/
lemma V_energy {p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) :
    energy f = (16 ^ p / 2) * ∑ k ∈ Finset.range (16 ^ p),
      (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p)) ^ 2 := by
  have hL : (0 : ℝ) < 16 ^ p := by positivity
  set a : ℕ → ℝ := fun k => (k : ℝ) / 16 ^ p with ha
  have hpiece : ∀ k : ℕ, k < 16 ^ p → EqOn (fun x => (deriv f x) ^ 2)
      (fun _ => (16 ^ p * (f (((k : ℝ) + 1) / 16 ^ p) - f ((k : ℝ) / 16 ^ p))) ^ 2)
      (Ioo (a k) (a (k + 1))) := by
    intro k hk x hx
    have hx' : x ∈ Ioo ((k : ℝ) / 16 ^ p) (((k : ℝ) + 1) / 16 ^ p) := by
      simpa [ha] using hx
    simp only [(V_hasDerivAt hf hk hx').deriv]
  have hle : ∀ k, a k ≤ a (k + 1) := by
    intro k; simp only [ha]; gcongr; linarith
  have hint : ∀ k : ℕ, k < 16 ^ p → IntervalIntegrable (fun x => (deriv f x) ^ 2) volume
      (a k) (a (k + 1)) := by
    intro k hk
    refine (intervalIntegrable_const (c := (16 ^ p * (f (((k : ℝ) + 1) / 16 ^ p) -
      f ((k : ℝ) / 16 ^ p))) ^ 2)).congr_uIoo ?_
    rw [uIoo_of_le (hle k)]
    exact (hpiece k hk).symm
  have h0 : a 0 = 0 := by simp [ha]
  have h1 : a (16 ^ p) = 1 := by simp [ha, hL.ne']
  unfold energy
  rw [← h0, ← h1, ← intervalIntegral.sum_integral_adjacent_intervals hint, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_congr_Ioo_of_le (hle k) (hpiece k (Finset.mem_range.1 hk)),
    intervalIntegral.integral_const]
  simp only [ha, smul_eq_mul]
  push_cast
  field_simp
  ring


/-! ## The coarse interpolant -/

/-- Linear interpolation of `f` on the mesh `16⁻ⁿ`.  Writing `k = ⌊16ⁿ x⌋` and
`t = 16ⁿ x - k`, it is `(1 - t) f(k 16⁻ⁿ) + t f((k+1) 16⁻ⁿ)`. -/
def coarse (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - ((16 : ℝ) ^ n * x - ((⌊(16 : ℝ) ^ n * x⌋ : ℤ) : ℝ))) *
      f (((⌊(16 : ℝ) ^ n * x⌋ : ℤ) : ℝ) / 16 ^ n) +
    ((16 : ℝ) ^ n * x - ((⌊(16 : ℝ) ^ n * x⌋ : ℤ) : ℝ)) *
      f ((((⌊(16 : ℝ) ^ n * x⌋ : ℤ) : ℝ) + 1) / 16 ^ n)

lemma coarse_piece (n : ℕ) (f : ℝ → ℝ) (k : ℤ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n)) :
    coarse n f x = (1 - (16 ^ n * x - k)) * f ((k : ℝ) / 16 ^ n) +
      (16 ^ n * x - k) * f (((k : ℝ) + 1) / 16 ^ n) := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have h1 : (k : ℝ) ≤ 16 ^ n * x := by
    have := hx.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : 16 ^ n * x ≤ (k : ℝ) + 1 := by
    have := hx.2; rw [le_div_iff₀ hN] at this; linarith
  rcases h2.lt_or_eq with h2 | h2
  · have hfl : ⌊(16 : ℝ) ^ n * x⌋ = k := Int.floor_eq_iff.2 ⟨h1, h2⟩
    rw [coarse, hfl]
  · have hfl : ⌊(16 : ℝ) ^ n * x⌋ = k + 1 := by
      rw [h2]; exact_mod_cast Int.floor_intCast (k + 1)
    rw [coarse, hfl, h2]
    push_cast
    ring

lemma coarse_piece_nat (n : ℕ) (f : ℝ → ℝ) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n)) :
    coarse n f x = (1 - (16 ^ n * x - k)) * f ((k : ℝ) / 16 ^ n) +
      (16 ^ n * x - k) * f (((k : ℝ) + 1) / 16 ^ n) := by
  have := coarse_piece n f (k : ℤ) (x := x) (by simpa using hx)
  simpa using this

lemma coarse_node (n : ℕ) (f : ℝ → ℝ) (y : ℝ) (hy : ∃ j : ℤ, (j : ℝ) = y) :
    coarse n f (y / 16 ^ n) = f (y / 16 ^ n) := by
  obtain ⟨j, rfl⟩ := hy
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have e : (16 : ℝ) ^ n * ((j : ℝ) / 16 ^ n) = j := by field_simp
  rw [coarse, e, Int.floor_intCast]
  simp

lemma zero_of_le_of_zero {f : ℝ → ℝ} (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hout : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) : f x = 0 := by
  by_cases hx' : x ∈ Icc (0 : ℝ) 1
  · rcases hx with hx | hx
    · rw [le_antisymm hx hx'.1]; exact h0
    · rw [le_antisymm hx'.2 hx]; exact h1
  · exact hout x hx'

lemma coarse_mem (n : ℕ) {f : ℝ → ℝ} (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hout : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) : coarse n f ∈ V n := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have hz := fun x hx => zero_of_le_of_zero h0 h1 hout (x := x) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := coarse_node n f 0 ⟨0, by simp⟩
    simpa [h0] using this
  · have := coarse_node n f (16 ^ n) ⟨16 ^ n, by push_cast; ring⟩
    rw [div_self hN.ne'] at this
    rw [this, h1]
  · intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    have hk : ∀ k : ℤ, k = ⌊(16 : ℝ) ^ n * x⌋ →
        f ((k : ℝ) / 16 ^ n) = 0 ∧ f (((k : ℝ) + 1) / 16 ^ n) = 0 := by
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
      · have hk0 : (16 : ℤ) ^ n ≤ k := by
          rw [hk, Int.le_floor]; push_cast; nlinarith
        have hk0' : (16 : ℝ) ^ n ≤ k := by exact_mod_cast hk0
        constructor
        · apply hz; right; rw [le_div_iff₀ hN]; linarith
        · apply hz; right; rw [le_div_iff₀ hN]; linarith
    obtain ⟨e1, e2⟩ := hk _ rfl
    rw [coarse, e1, e2]
    ring
  · intro k hk
    refine ⟨16 ^ n * (f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)),
      f ((k : ℝ) / 16 ^ n) - k * (f (((k : ℝ) + 1) / 16 ^ n) - f ((k : ℝ) / 16 ^ n)),
      fun x hx => ?_⟩
    rw [coarse_piece_nat n f k hx]
    ring

/-! ## The rescaled fine pieces -/

/-- The fine part `f - coarse n f` on the `k`-th coarse interval, rescaled to `[0,1]`:
`t ↦ 16ⁿ (f - g)((k + t) 16⁻ⁿ)` for `t ∈ [0,1]`, and `0` otherwise. -/
def fine (n : ℕ) (f : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  if t ∈ Icc (0 : ℝ) 1 then
    (16 : ℝ) ^ n * (f (((k : ℝ) + t) / 16 ^ n) -
      ((1 - t) * f ((k : ℝ) / 16 ^ n) + t * f (((k : ℝ) + 1) / 16 ^ n)))
  else 0

lemma fine_mem {n m : ℕ} {f : ℝ → ℝ} (hf : f ∈ V (n + m)) {k : ℕ} (hk : k < 16 ^ n) :
    fine n f k ∈ V m := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have hM : (0 : ℝ) < 16 ^ m := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [fine]
  · simp [fine]
  · intro x hx; simp [fine, hx]
  · intro i hi
    have hj : k * 16 ^ m + i < 16 ^ (n + m) := by
      rw [pow_add]
      have : k + 1 ≤ 16 ^ n := hk
      nlinarith
    have hi' : (i : ℝ) + 1 ≤ 16 ^ m := by
      have : i + 1 ≤ 16 ^ m := hi
      exact_mod_cast this
    have hjc : (((k * 16 ^ m + i : ℕ) : ℝ)) = (k : ℝ) * 16 ^ m + i := by push_cast; ring
    refine ⟨16 ^ n * (16 ^ m * (f ((((k * 16 ^ m + i : ℕ) : ℝ) + 1) / 16 ^ (n + m)) -
        f (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m))) +
        f ((k : ℝ) / 16 ^ n) - f (((k : ℝ) + 1) / 16 ^ n)),
      16 ^ n * (f (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m)) -
        i * (f ((((k * 16 ^ m + i : ℕ) : ℝ) + 1) / 16 ^ (n + m)) -
        f (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m))) - f ((k : ℝ) / 16 ^ n)),
      fun t ht => ?_⟩
    have ht1 : (i : ℝ) ≤ t * 16 ^ m := by
      have := ht.1; rwa [div_le_iff₀ hM] at this
    have ht2 : t * 16 ^ m ≤ (i : ℝ) + 1 := by
      have := ht.2; rwa [le_div_iff₀ hM] at this
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        nlinarith
      · nlinarith
    have hy : ((k : ℝ) + t) / 16 ^ n ∈ Icc (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m))
        ((((k * 16 ^ m + i : ℕ) : ℝ) + 1) / 16 ^ (n + m)) := by
      rw [hjc, pow_add]
      constructor
      · rw [div_le_div_iff₀ (by positivity) hN]
        nlinarith [mul_le_mul_of_nonneg_left ht1 hN.le]
      · rw [div_le_div_iff₀ hN (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left ht2 hN.le]
    rw [fine, ite_eq_left ht01, V_piece hf hj hy]
    have e : (16 : ℝ) ^ (n + m) * (((k : ℝ) + t) / 16 ^ n) - ((k * 16 ^ m + i : ℕ) : ℝ) =
        16 ^ m * t - i := by
      rw [hjc, pow_add]; field_simp; ring
    rw [e]
    ring

lemma fine_node (n m : ℕ) (f : ℝ → ℝ) (k : ℕ) {i : ℕ} (hi : i ≤ 16 ^ m) :
    fine n f k ((i : ℝ) / 16 ^ m) = 16 ^ n * (f (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m)) -
      ((1 - (i : ℝ) / 16 ^ m) * f ((k : ℝ) / 16 ^ n) +
        ((i : ℝ) / 16 ^ m) * f (((k : ℝ) + 1) / 16 ^ n))) := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have hM : (0 : ℝ) < 16 ^ m := by positivity
  have hi' : (i : ℝ) ≤ 16 ^ m := by exact_mod_cast hi
  have h01 : (i : ℝ) / 16 ^ m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hM]; exact hi'
  have e : ((k : ℝ) + (i : ℝ) / 16 ^ m) / 16 ^ n =
      ((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m) := by
    push_cast; rw [pow_add]; field_simp
  rw [fine, ite_eq_left h01, e]

/-- On the `k`-th coarse interval, `f = g + 16⁻ⁿ ũ_k(16ⁿ x - k)`. -/
lemma decomp_piece (n : ℕ) (f : ℝ → ℝ) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n)) :
    f x = coarse n f x + (1 / 16 ^ n) * fine n f k (16 ^ n * x - k) := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have h1 : (k : ℝ) ≤ 16 ^ n * x := by
    have := hx.1; rw [div_le_iff₀ hN] at this; linarith
  have h2 : 16 ^ n * x ≤ (k : ℝ) + 1 := by
    have := hx.2; rw [le_div_iff₀ hN] at this; linarith
  have ht : 16 ^ n * x - k ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have e : ((k : ℝ) + (16 ^ n * x - k)) / 16 ^ n = x := by field_simp; ring
  rw [coarse_piece_nat n f k hx, fine, ite_eq_left ht, e]
  field_simp
  ring

/-! ## Energy decomposition -/

lemma sum_range_mul_split (N M : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N * M), h j =
      ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range M, h (k * M + i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The algebraic identity behind `E(f) = E(g) + E(u)` on one coarse interval. -/
lemma block_identity (A U : ℕ → ℝ) (M : ℕ) (hM : 0 < M) (N L Mr : ℝ) (hN : 0 < N)
    (hMr : Mr = M) (hL : L = N * Mr)
    (hU : ∀ i ≤ M, U i = N * (A i - ((1 - (i : ℝ) / Mr) * A 0 + ((i : ℝ) / Mr) * A M))) :
    L / 2 * ∑ i ∈ Finset.range M, (A (i + 1) - A i) ^ 2 =
      N / 2 * (A M - A 0) ^ 2 + 1 / N * (Mr / 2 * ∑ i ∈ Finset.range M, (U (i + 1) - U i) ^ 2) := by
  subst hL hMr
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set D := A M - A 0 with hD
  have key : ∀ i ∈ Finset.range M, (U (i + 1) - U i) ^ 2 =
      N ^ 2 * (A (i + 1) - A i) ^ 2 - (2 * N ^ 2 * D / M) * (A (i + 1) - A i) +
        N ^ 2 * D ^ 2 / M ^ 2 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [hU (i + 1) hi', hU i hi'.le, hD]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_range_sub A M, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp
  ring

lemma energy_decomp {n m : ℕ} {f : ℝ → ℝ} (hf : f ∈ V (n + m)) :
    energy f = energy (coarse n f) +
      ∑ k ∈ Finset.range (16 ^ n), (1 / 16 ^ n) * energy (fine n f k) := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have hM : (0 : ℝ) < 16 ^ m := by positivity
  have hg := coarse_mem n hf.1 hf.2.1 hf.2.2.1
  have hsplit : energy f = ∑ k ∈ Finset.range (16 ^ n), (16 : ℝ) ^ (n + m) / 2 *
      ∑ i ∈ Finset.range (16 ^ m), (f ((((k * 16 ^ m + i : ℕ) : ℝ) + 1) / 16 ^ (n + m)) -
        f (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m))) ^ 2 := by
    rw [V_energy hf, ← Finset.mul_sum, show (16 : ℕ) ^ (n + m) = 16 ^ n * 16 ^ m from pow_add 16 n m,
      sum_range_mul_split]
  rw [hsplit, V_energy hg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [V_energy (fine_mem hf (Finset.mem_range.1 hk)), coarse_node n f ((k : ℝ) + 1) ⟨k + 1, by simp⟩,
    coarse_node n f (k : ℝ) ⟨k, by simp⟩]
  set A : ℕ → ℝ := fun i => f (((k * 16 ^ m + i : ℕ) : ℝ) / 16 ^ (n + m)) with hA
  set U : ℕ → ℝ := fun i => fine n f k ((i : ℝ) / 16 ^ m) with hU
  have hA0 : A 0 = f ((k : ℝ) / 16 ^ n) := by
    simp only [hA]; congr 1
    rw [pow_add, div_eq_div_iff (by positivity) (by positivity)]; push_cast; ring
  have hAM : A (16 ^ m) = f (((k : ℝ) + 1) / 16 ^ n) := by
    simp only [hA]; congr 1
    rw [pow_add, div_eq_div_iff (by positivity) (by positivity)]; push_cast; ring
  have hF1 : ∀ i : ℕ, f ((((k * 16 ^ m + i : ℕ) : ℝ) + 1) / 16 ^ (n + m)) = A (i + 1) := by
    intro i; simp only [hA]; congr 2; push_cast; ring
  have hF2 : ∀ i : ℕ, fine n f k (((i : ℝ) + 1) / 16 ^ m) = U (i + 1) := by
    intro i; simp only [hU]; push_cast; rfl
  have hUA : ∀ i ≤ 16 ^ m, U i =
      16 ^ n * (A i - ((1 - (i : ℝ) / 16 ^ m) * A 0 + ((i : ℝ) / 16 ^ m) * A (16 ^ m))) := by
    intro i hi
    rw [hA0, hAM]
    exact fine_node n m f k hi
  simp only [hF1, hF2]
  rw [← hA0, ← hAM]
  exact block_identity A U (16 ^ m) (by positivity) (16 ^ n) ((16 : ℝ) ^ (n + m)) (16 ^ m) hN
    (by push_cast; ring) (pow_add 16 n m) hUA

/-! ## `L¹` decomposition -/

lemma coarse_continuous {n p : ℕ} {f : ℝ → ℝ} (hf : f ∈ V p) : Continuous (coarse n f) :=
  V_continuous (coarse_mem n hf.1 hf.2.1 hf.2.2.1)

lemma l1_decomp {n m : ℕ} {f f' : ℝ → ℝ} (hf : f ∈ V (n + m)) (hf' : f' ∈ V (n + m)) :
    ∫ x in (0 : ℝ)..1, |f x - f' x| ≤ (∫ x in (0 : ℝ)..1, |coarse n f x - coarse n f' x|) +
      ∑ k ∈ Finset.range (16 ^ n),
        (1 / 16 ^ n) ^ 2 * ∫ t in (0 : ℝ)..1, |fine n f k t - fine n f' k t| := by
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  have hfc := V_continuous hf
  have hfc' := V_continuous hf'
  have hgc := coarse_continuous (n := n) hf
  have hgc' := coarse_continuous (n := n) hf'
  set a : ℕ → ℝ := fun k => (k : ℝ) / 16 ^ n with ha
  have h0 : a 0 = 0 := by simp [ha]
  have h1 : a (16 ^ n) = 1 := by simp [ha, hN.ne']
  have hle : ∀ k, a k ≤ a (k + 1) := by
    intro k; simp only [ha]; gcongr; linarith
  have split1 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a)
    (n := 16 ^ n) (f := fun x => |f x - f' x|)
    (fun k _ => ((hfc.sub hfc').abs).intervalIntegrable _ _)
  have split2 := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a)
    (n := 16 ^ n) (f := fun x => |coarse n f x - coarse n f' x|)
    (fun k _ => ((hgc.sub hgc').abs).intervalIntegrable _ _)
  rw [h0, h1] at split1 split2
  rw [← split1, ← split2, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have huc := V_continuous (fine_mem hf hk')
  have huc' := V_continuous (fine_mem hf' hk')
  have hcomp : Continuous fun x : ℝ =>
      |fine n f k (16 ^ n * x - k) - fine n f' k (16 ^ n * x - k)| := by
    fun_prop
  calc ∫ x in a k..a (k + 1), |f x - f' x|
      ≤ ∫ x in a k..a (k + 1), (|coarse n f x - coarse n f' x| +
          (1 / 16 ^ n) * |fine n f k (16 ^ n * x - k) - fine n f' k (16 ^ n * x - k)|) := by
        refine intervalIntegral.integral_mono_on (hle k)
          (((hfc.sub hfc').abs).intervalIntegrable _ _)
          ((((hgc.sub hgc').abs).add (continuous_const.mul hcomp)).intervalIntegrable _ _)
          fun x hx => ?_
        have hx' : x ∈ Icc ((k : ℝ) / 16 ^ n) (((k : ℝ) + 1) / 16 ^ n) := by
          simpa [ha] using hx
        rw [decomp_piece n f k hx', decomp_piece n f' k hx']
        have e : coarse n f x + 1 / 16 ^ n * fine n f k (16 ^ n * x - k) -
            (coarse n f' x + 1 / 16 ^ n * fine n f' k (16 ^ n * x - k)) =
            (coarse n f x - coarse n f' x) +
              (1 / 16 ^ n) * (fine n f k (16 ^ n * x - k) - fine n f' k (16 ^ n * x - k)) := by
          ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 16 ^ n)]
    _ = (∫ x in a k..a (k + 1), |coarse n f x - coarse n f' x|) +
          (1 / 16 ^ n) ^ 2 * ∫ t in (0 : ℝ)..1, |fine n f k t - fine n f' k t| := by
        have i1 : IntervalIntegrable (fun x => |coarse n f x - coarse n f' x|) volume
            (a k) (a (k + 1)) := ((hgc.sub hgc').abs).intervalIntegrable _ _
        have i2 : IntervalIntegrable (fun x => 1 / 16 ^ n *
            |fine n f k (16 ^ n * x - k) - fine n f' k (16 ^ n * x - k)|) volume
            (a k) (a (k + 1)) := (continuous_const.mul hcomp).intervalIntegrable _ _
        rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul]
        have hsub := intervalIntegral.integral_comp_mul_sub (a := a k) (b := a (k + 1))
          (fun t => |fine n f k t - fine n f' k t|) hN.ne' (k : ℝ)
        rw [hsub]
        have e1 : (16 : ℝ) ^ n * a k - k = 0 := by simp only [ha]; field_simp; ring
        have e2 : (16 : ℝ) ^ n * a (k + 1) - k = 1 := by
          simp only [ha]; push_cast; field_simp; ring
        rw [e1, e2, smul_eq_mul]
        ring

/-! ## Canonical distance -/

lemma zCov_dist_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : (ℝ → ℝ) → E) {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (haa : ⟪T a, T a⟫ = zCov a a) (hbb : ⟪T b, T b⟫ = zCov b b)
    (hab : ⟪T a, T b⟫ = zCov a b) :
    ‖T a - T b‖ ^ 2 = 2 * π * ∫ x in (0 : ℝ)..1, |a x - b x| := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, haa, hbb,
    hab]
  have ia : IntervalIntegrable (fun x => |a x|) volume 0 1 := (ha.abs).intervalIntegrable 0 1
  have ib : IntervalIntegrable (fun x => |b x|) volume 0 1 := (hb.abs).intervalIntegrable 0 1
  have iab : IntervalIntegrable (fun x => |a x - b x|) volume 0 1 :=
    ((ha.sub hb).abs).intervalIntegrable 0 1
  have e1 : ∀ c : ℝ → ℝ, zCov c c = π * (2 * ∫ x in (0 : ℝ)..1, |c x|) := by
    intro c
    have : ∀ x : ℝ, |c x| + |c x| - |c x - c x| = 2 * |c x| := fun x => by
      simp only [sub_self, abs_zero, sub_zero]; ring
    simp only [zCov, this, intervalIntegral.integral_const_mul]
  have e2 : zCov a b = π * ((∫ x in (0 : ℝ)..1, |a x|) + (∫ x in (0 : ℝ)..1, |b x|) -
      ∫ x in (0 : ℝ)..1, |a x - b x|) := by
    unfold zCov
    rw [intervalIntegral.integral_sub (ia.add ib) iab, intervalIntegral.integral_add ia ib]
  rw [e1 a, e1 b, e2]
  ring

end LQGDimension.Subadd
