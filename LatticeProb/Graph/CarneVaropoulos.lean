import Mathlib
import LatticeProb.Graph.ChebyshevWalk
import LatticeProb.Graph.ExitTime
import LatticeProb.Network.Killed
import LatticeProb.Graph.Reach

/-!
# The Carne–Varopoulos bound

For the simple random walk on a connected, nontrivial, locally finite graph,
`P_x(X_n = y) ≤ 2 √(deg y / deg x) e^{-dist(x, y)²/(2n)}` (`walkLaw_eval_le_carneVaropoulos`;
T. K. Carne, 1985, N. Varopoulos, 1985, Lyons–Peres, *Probability on Trees and Networks*,
Theorem 13.4), and the same bound for the heat kernel of any locally finite graph without
isolated vertices (`heat_le_carneVaropoulos`).

The proof is Carne's. At time `n` the walk from `x` stays in the ball `B` of radius `n` about `x`,
where `p_n(x, y)` is the `(x, y)` entry of `Qⁿ` for the transition matrix `Q` of the walk killed
off `B` (`heat_eq_transMat_pow`). Conjugating by `√deg` turns `Q` into the symmetric matrix `A`
(`transMat_pow_eq`), whose eigenvalues lie in `[-1, 1]`. In the Chebyshev expansion
`Aⁿ = ∑_k p_n(k) T_k(A)` of `LatticeProb.Graph.ChebyshevWalk`, `|T_k(A)_{xy}| ≤ 1`, and
`T_k(A)_{xy} = 0` for `|k| < dist(x, y)` since `T_k` has degree `|k|`
(`aeval_symMat_apply_eq_zero`); so `Aⁿ_{xy}` is at most the tail `∑_{|k| ≥ dist} p_n(k)` of
the walk on `ℤ`, and Hoeffding's bound finishes.
-/

open MeasureTheory Polynomial
open scoped ENNReal

noncomputable section

namespace LatticeProb.Graph

section Ball

open scoped Classical

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-! ### The walk on a finite ball -/

/-- The endpoint of a walk of length `m` from `a` is in `reach G m a`. -/
theorem mem_reach_of_walk {a b : V} (p : G.Walk a b) : b ∈ reach G p.length a := by
  induction p with
  | nil => rw [SimpleGraph.Walk.length_nil, reach_zero, Finset.mem_singleton]
  | cons hadj q ih =>
      rw [SimpleGraph.Walk.length_cons, reach_succ, Finset.mem_biUnion]
      exact ⟨_, (SimpleGraph.mem_neighborFinset _ _ _).2 hadj, ih⟩

/-- The centre of a ball is in it. -/
theorem self_mem_ballFinset (x : V) (r : ℕ) : x ∈ ballFinset G x r := by
  rw [ballFinset, Finset.mem_biUnion]
  exact ⟨0, Finset.mem_range.2 (by omega), by rw [reach_zero, Finset.mem_singleton]⟩

/-- Balls grow with the radius. -/
theorem ballFinset_mono (x : V) {i j : ℕ} (h : i ≤ j) :
    ballFinset G x i ⊆ ballFinset G x j := by
  intro v hv
  rw [ballFinset, Finset.mem_biUnion] at hv ⊢
  obtain ⟨m, hm, hv⟩ := hv
  exact ⟨m, Finset.mem_range.2 (by rw [Finset.mem_range] at hm; omega), hv⟩

/-- A neighbour of a vertex of the ball of radius `i` is in the ball of radius `i + 1`. -/
theorem mem_ballFinset_succ_of_adj {x u z : V} {i : ℕ} (hu : u ∈ ballFinset G x i)
    (h : G.Adj u z) : z ∈ ballFinset G x (i + 1) := by
  rw [ballFinset, Finset.mem_biUnion] at hu ⊢
  obtain ⟨m, hm, hu⟩ := hu
  obtain ⟨p, hp⟩ := exists_walk_of_mem_reach m x u hu
  refine ⟨m + 1, Finset.mem_range.2 (by rw [Finset.mem_range] at hm; omega), ?_⟩
  have := mem_reach_of_walk G (p.concat h)
  rwa [SimpleGraph.Walk.length_concat, hp] at this

/-- A connected locally finite graph has countably many vertices. -/
theorem countable_of_connected (hG : G.Connected) : Countable V := by
  obtain ⟨x⟩ := hG.nonempty
  have hcover : (Set.univ : Set V) ⊆ ⋃ n : ℕ, ((reach G n x : Finset V) : Set V) := by
    intro v _
    obtain ⟨p⟩ := hG.preconnected x v
    exact Set.mem_iUnion.2 ⟨p.length, mem_reach_of_walk G p⟩
  exact Set.countable_univ_iff.mp
    ((Set.countable_iUnion fun n => (reach G n x).countable_toSet).mono hcover)

/-- The transition matrix of the walk killed off `S`: `Q u v = 1{u ∼ v} / deg u`. -/
def transMat (S : Finset V) : Matrix S S ℝ :=
  fun u v => if G.Adj u v then ((G.degree u : ℝ))⁻¹ else 0

/-- The symmetrized transition matrix `A u v = 1{u ∼ v} / √(deg u deg v)`. -/
def symMat (S : Finset V) : Matrix S S ℝ :=
  fun u v => if G.Adj u v then (Real.sqrt ((G.degree u : ℝ) * G.degree v))⁻¹ else 0

/-- On the ball `B` of radius `n` about `x`, `p_j(u, y)` is the `(u, y)` entry of the `j`-th
power of the transition matrix of the walk killed off `B`, when `u` is within `i` steps of `x`
and `i + j ≤ n`: a walk of `j` steps from `u` does not leave `B`. -/
theorem heat_eq_transMat_pow (x : V) (n : ℕ) {i j : ℕ} (hij : i + j ≤ n) {u y : V}
    (hu : u ∈ ballFinset G x i) (hy : y ∈ ballFinset G x n) :
    heat G j u y
      = (transMat G (ballFinset G x n) ^ j)
          ⟨u, ballFinset_mono G x (by omega) hu⟩ ⟨y, hy⟩ := by
  set S := ballFinset G x n
  induction j generalizing i u with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      show (if u = y then (1 : ℝ) else 0) = _
      by_cases h : u = y
      · subst h; simp
      · rw [if_neg h, if_neg (fun h' => h (congrArg Subtype.val h'))]
  | succ j ih =>
      set Q := transMat G S
      have hN : G.neighborFinset u ⊆ S := fun z hz =>
        ballFinset_mono G x (by omega)
          (mem_ballFinset_succ_of_adj G hu ((G.mem_neighborFinset u z).1 hz))
      set F : V → ℝ := fun z =>
        if h : z ∈ S then
          Q ⟨u, ballFinset_mono G x (by omega) hu⟩ ⟨z, h⟩ * (Q ^ j) ⟨z, h⟩ ⟨y, hy⟩
        else 0 with hF
      have hsum : ∑ w : S, Q ⟨u, ballFinset_mono G x (by omega) hu⟩ w * (Q ^ j) w ⟨y, hy⟩
          = ∑ z ∈ S, F z := by
        rw [← Finset.sum_coe_sort S F]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hF]; dsimp only; rw [dif_pos w.2]
      have hzero : ∀ z ∈ S, z ∉ G.neighborFinset u → F z = 0 := by
        intro z hz hzN
        rw [hF]; dsimp only; rw [dif_pos hz]
        have hadj : ¬ G.Adj u z := fun h => hzN ((G.mem_neighborFinset u z).2 h)
        simp only [Q, transMat, if_neg hadj, zero_mul]
      have hnb : ∀ z ∈ G.neighborFinset u, F z = (G.degree u : ℝ)⁻¹ * heat G j z y := by
        intro z hz
        have hadj : G.Adj u z := (G.mem_neighborFinset u z).1 hz
        rw [hF]; dsimp only; rw [dif_pos (hN hz)]
        simp only [Q, transMat, if_pos hadj]
        rw [ih (i := i + 1) (by omega) (mem_ballFinset_succ_of_adj G hu hadj)]
      show walkOp G (fun z => heat G j z y) u = _
      rw [pow_succ', Matrix.mul_apply, hsum, ← Finset.sum_subset hN hzero,
        Finset.sum_congr rfl hnb, ← Finset.mul_sum, walkOp, div_eq_inv_mul]

/-- At time `n` the walk from `x` is in the ball of radius `n` about `x`. -/
theorem heat_eq_zero_of_notMem_ballFinset (x y : V) (n : ℕ) (hy : y ∉ ballFinset G x n) :
    heat G n x y = 0 := by
  refine heat_eq_zero_of_notMem_reach n x y fun h => hy ?_
  rw [ballFinset, Finset.mem_biUnion]
  exact ⟨n, Finset.mem_range.2 (by omega), h⟩

/-- The symmetrized transition matrix is symmetric. -/
theorem symMat_isHermitian (S : Finset V) : (symMat G S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun u v => ?_
  simp only [symMat, star_trivial]
  by_cases h : G.Adj (u : V) v
  · rw [if_pos h.symm, if_pos h, mul_comm]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

/-- The symmetrized transition matrix is `A u v = √(deg u) Q u v / √(deg v)`. -/
theorem symMat_eq (hdeg : ∀ v : V, 0 < G.degree v) (S : Finset V) (u v : S) :
    symMat G S u v
      = Real.sqrt (G.degree (u : V)) * transMat G S u v / Real.sqrt (G.degree (v : V)) := by
  have hu : (0 : ℝ) < G.degree (u : V) := by exact_mod_cast hdeg u
  have hv : (0 : ℝ) < G.degree (v : V) := by exact_mod_cast hdeg v
  simp only [symMat, transMat]
  by_cases h : G.Adj (u : V) v
  · rw [if_pos h, if_pos h, Real.sqrt_mul hu.le]
    set a := Real.sqrt (G.degree (u : V) : ℝ) with ha
    have ha0 : 0 < a := Real.sqrt_pos.mpr hu
    have hb0 : 0 < Real.sqrt (G.degree (v : V) : ℝ) := Real.sqrt_pos.mpr hv
    have hsq : (G.degree (u : V) : ℝ) = a * a := (Real.mul_self_sqrt hu.le).symm
    rw [hsq]
    field_simp
  · rw [if_neg h, if_neg h, mul_zero, zero_div]

/-- Powers of the killed transition matrix through the symmetrized one:
`Qʲ u v = √(deg v) / √(deg u) · Aʲ u v`. -/
theorem transMat_pow_eq (hdeg : ∀ v : V, 0 < G.degree v) (S : Finset V) (j : ℕ) (u v : S) :
    (transMat G S ^ j) u v
      = Real.sqrt (G.degree (v : V)) / Real.sqrt (G.degree (u : V)) * (symMat G S ^ j) u v := by
  have hpos : ∀ w : S, 0 < Real.sqrt (G.degree (w : V) : ℝ) :=
    fun w => Real.sqrt_pos.mpr (by exact_mod_cast hdeg w)
  have hQ : ∀ a b : S, transMat G S a b
      = Real.sqrt (G.degree (b : V)) / Real.sqrt (G.degree (a : V)) * symMat G S a b := by
    intro a b
    rw [symMat_eq G hdeg S a b]
    field_simp [(hpos a).ne', (hpos b).ne']
  induction j generalizing u with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.one_apply]
      by_cases h : u = v
      · subst h; rw [if_pos rfl, div_self (hpos u).ne', one_mul]
      · rw [if_neg h, mul_zero]
  | succ j ih =>
      rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hQ u w, ih w]
      field_simp [(hpos u).ne', (hpos w).ne']

/-- The killed transition matrix is nonnegative. -/
theorem transMat_nonneg (S : Finset V) (u v : S) : 0 ≤ transMat G S u v := by
  simp only [transMat]
  split_ifs <;> positivity

/-- The killed transition matrix is substochastic. -/
theorem sum_transMat_le_one (hdeg : ∀ v : V, 0 < G.degree v) (S : Finset V) (u : S) :
    ∑ v, transMat G S u v ≤ 1 := by
  have hdu : (0 : ℝ) < G.degree (u : V) := by exact_mod_cast hdeg u
  simp only [transMat]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun v : S => G.Adj (u : V) v).card
      ≤ (G.neighborFinset (u : V)).card := by
    refine Finset.card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn
    intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
    exact (G.mem_neighborFinset _ _).2 hv
  rw [G.card_neighborFinset_eq_degree] at hcard
  have hcard' : ((Finset.univ.filter fun v : S => G.Adj (u : V) v).card : ℝ)
      ≤ G.degree (u : V) := by exact_mod_cast hcard
  calc ((Finset.univ.filter fun v : S => G.Adj (u : V) v).card : ℝ)
        * ((G.degree (u : V) : ℝ))⁻¹
      ≤ G.degree (u : V) * ((G.degree (u : V) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hcard' (inv_nonneg.mpr hdu.le)
    _ = 1 := mul_inv_cancel₀ hdu.ne'

/-- The entries of `p(A)` vanish between vertices farther apart than the degree of `p`,
since `(Aʲ) u v = 0` unless a walk of `j` steps joins `u` to `v`. -/
theorem aeval_symMat_apply_eq_zero (S : Finset V) (p : ℝ[X]) (u v : S)
    (hp : p.natDegree < G.dist u v) : (aeval (symMat G S) p) u v = 0 := by
  have hwalk : ∀ (j : ℕ) (a b : S), (symMat G S ^ j) a b ≠ 0 →
      ∃ q : G.Walk (a : V) b, q.length = j := by
    intro j
    induction j with
    | zero =>
        intro a b h
        rw [pow_zero, Matrix.one_apply] at h
        split_ifs at h with hab
        · subst hab; exact ⟨SimpleGraph.Walk.nil, rfl⟩
        · exact absurd rfl h
    | succ j ih =>
        intro a b h
        rw [pow_succ', Matrix.mul_apply] at h
        obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
        have hadj : G.Adj (a : V) w := by
          by_contra hna
          apply hw
          simp only [symMat, if_neg hna, zero_mul]
        obtain ⟨q, hq⟩ := ih w b (fun h0 => hw (by rw [h0, mul_zero]))
        exact ⟨SimpleGraph.Walk.cons hadj q, by rw [SimpleGraph.Walk.length_cons, hq]⟩
  have hzero : ∀ j, j < G.dist u v → (symMat G S ^ j) u v = 0 := by
    intro j hj
    by_contra h
    obtain ⟨q, hq⟩ := hwalk j u v h
    have := SimpleGraph.dist_le q
    omega
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Matrix.smul_apply, hzero j (by rw [Finset.mem_range] at hj; omega), smul_zero]

/-! ### The Carne–Varopoulos bound -/

/-- **The Carne–Varopoulos bound** (Carne 1985, Varopoulos 1985; Lyons–Peres, Theorem 13.4)
for the heat kernel of a locally finite graph without isolated vertices:
`p_n(x, y) ≤ 2 √(deg y / deg x) e^{-dist(x, y)²/(2n)}`. -/
theorem heat_le_carneVaropoulos (hdeg : ∀ v : V, 0 < G.degree v) (x y : V) (n : ℕ)
    (hn : 1 ≤ n) :
    heat G n x y
      ≤ 2 * Real.sqrt ((G.degree y : ℝ) / G.degree x)
          * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by
  set S := ballFinset G x n
  have hdx : (0 : ℝ) < G.degree x := by exact_mod_cast hdeg x
  have hRHS : 0 ≤ 2 * Real.sqrt ((G.degree y : ℝ) / G.degree x)
      * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by positivity
  by_cases hy : y ∈ S
  swap
  · rw [heat_eq_zero_of_notMem_ballFinset G x y n hy]; exact hRHS
  have hx : x ∈ S := self_mem_ballFinset G x n
  set x' : S := ⟨x, hx⟩
  set y' : S := ⟨y, hy⟩
  set A := symMat G S with hAdef
  have hA : A.IsHermitian := symMat_isHermitian G S
  have hev : ∀ i, |hA.eigenvalues i| ≤ 1 :=
    abs_eigenvalues_le_one hA (transMat_nonneg G S) (sum_transMat_le_one G hdeg S)
      (fun u : S => Real.sqrt (G.degree (u : V)))
      (fun u => Real.sqrt_pos.mpr (by exact_mod_cast hdeg u)) (symMat_eq G hdeg S)
  have h1 : heat G n x y = (transMat G S ^ n) x' y' :=
    heat_eq_transMat_pow G x n (i := 0) (by omega) (self_mem_ballFinset G x 0) hy
  have hpow : (A ^ n) x' y'
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y' := by
    rw [← aeval_X_pow (R := ℝ) A (n := n), X_pow_eq_sum_lineWalk_T, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_C, ← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]
  have hterm : ∀ k ∈ Finset.Icc (-(n : ℤ)) n,
      lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y'
        ≤ if (G.dist x y : ℝ) ≤ |(k : ℝ)| then lineWalk n k else 0 := by
    intro k _
    split_ifs with hk
    · calc lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y'
          ≤ lineWalk n k * |(aeval A (Chebyshev.T ℝ k)) x' y'| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (lineWalk_nonneg n k)
        _ ≤ lineWalk n k * 1 :=
            mul_le_mul_of_nonneg_left (abs_aeval_T_apply_le_one hA hev k x' y')
              (lineWalk_nonneg n k)
        _ = lineWalk n k := mul_one _
    · have hlt : (Chebyshev.T ℝ k).natDegree < G.dist x y := by
        rw [Chebyshev.natDegree_T]
        have hcast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        have : ((k.natAbs : ℕ) : ℝ) < (G.dist x y : ℝ) := by rw [hcast]; linarith
        exact_mod_cast this
      rw [aeval_symMat_apply_eq_zero G S _ x' y' hlt, mul_zero]
  have hAn : (A ^ n) x' y' ≤ 2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by
    rw [hpow]
    calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n, lineWalk n k * (aeval A (Chebyshev.T ℝ k)) x' y'
        ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
            if (G.dist x y : ℝ) ≤ |(k : ℝ)| then lineWalk n k else 0 :=
          Finset.sum_le_sum hterm
      _ = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter
              (fun k : ℤ => (G.dist x y : ℝ) ≤ |(k : ℝ)|),
            lineWalk n k := (Finset.sum_filter _ _).symm
      _ ≤ 2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) :=
          sum_lineWalk_tail_le n hn _ (Nat.cast_nonneg _)
  rw [h1, transMat_pow_eq G hdeg S n x' y', Real.sqrt_div' _ hdx.le]
  have hq : 0 ≤ Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x) := by positivity
  calc Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x) * (A ^ n) x' y'
      ≤ Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x)
          * (2 * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n))) :=
        mul_le_mul_of_nonneg_left hAn hq
    _ = 2 * (Real.sqrt (G.degree y : ℝ) / Real.sqrt (G.degree x))
          * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := by ring

/-- **The Carne–Varopoulos bound** for the simple random walk on a connected, nontrivial,
locally finite graph: `P_x(X_n = y) ≤ 2 √(deg y / deg x) e^{-dist(x, y)²/(2n)}`. -/
theorem walkLaw_eval_le_carneVaropoulos [MeasurableSpace V] [MeasurableSingletonClass V]
    [Nontrivial V] (hG : G.Connected) (x y : V) (n : ℕ) (hn : 1 ≤ n) :
    walkLaw G x {X : ℕ → V | X n = y}
      ≤ ENNReal.ofReal (2 * Real.sqrt ((G.degree y : ℝ) / G.degree x)
          * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n))) := by
  haveI : Countable V := countable_of_connected G hG
  have hdeg : ∀ v : V, 0 < G.degree v := by
    intro v
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hG.preconnected v w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact G.degree_pos_iff_exists_adj v |>.mpr ⟨_, h⟩
  have hstay : {X : ℕ → V | X n = y} ∩ stayIn (Set.univ : Set V) n = {X | X n = y} := by
    ext X; simp [stayIn]
  have hreal := walkLaw_stayIn_eq_real (G := G) hdeg Set.univ n x y
  rw [hstay, LatticeProb.Network.killedHeat_univ] at hreal
  rw [← ENNReal.ofReal_toReal (measure_ne_top (walkLaw G x) _), ← measureReal_def, hreal]
  exact ENNReal.ofReal_le_ofReal (heat_le_carneVaropoulos G hdeg x y n hn)

end Ball

end LatticeProb.Graph
