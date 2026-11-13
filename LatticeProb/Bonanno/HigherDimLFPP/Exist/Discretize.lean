/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Discretize at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Paths.DistOn
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Clusters
import Mathlib.Algebra.Order.Round

/-!
# Discretization of the coarse path (DGZ Lemma 3.3, Step 2; packet P-X7a, target T1)

Source: DGZ arXiv:2310.03996, proof of Lemma 3.3, Step 2 ((3.19)–(3.21)); planning audit HA5,
finding G2 and Details D8 (the corrected discretization) and "Use (DGZ (3.20))".

Lattice conventions. Sites are `Perc.Zd d = Fin d → ℤ`; the site `x` of the lattice `s ℤ^d` is
the point `latPt s x = s x ∈ ℝ^d`. `latE1 d N = N e₁ ∈ ℤ^d`, so `latPt s (latE1 d N) = e₁` when
`s N = 1` (`latPt_latE1`). Boxes are `ℓ^∞` boxes: `cbox c r = c + [-r, r]^d` and
`obox c r = c + (-r, r)^d` (the frozen cube is `obox 0 2`, `cube_eq_obox`).

Main results (namespace `HigherDimLFPP.DGZ`):

* `exists_nodup_isChain_of_reflTransGen` (loop erasure): an L-path inside a set `S` contains a
  duplicate-free L-path inside `S` with the same endpoints.
* `exists_latticePath` (HA5 D8): for `s > 0` with `s N = 1` and a continuous path
  `P : [0,1] → U = (-2,2)^d` from `0` to `e₁`, there are distinct sites `x₁ = 0, …, x_J = N e₁`,
  consecutive ones L-adjacent, with `s x_j ∈ U` and `|s x_j - P(t_j)|_∞ < (5/4) s` for some `t_j`.
  Proof (HA5 D8): uniform continuity, rounding toward `0` (`roundLat`, so `s x_j` stays in `U`), the
  coordinate paths of `Perc.reflTransGen_cube` between consecutive rounded points, loop erasure.
* `sum_mul_exp_le` (HA5 "Use (DGZ (3.20))", the bound (3.20′)): if `6 s < 1`, the distinct sites
  `x ∈ X` are within `(5/4) s` of a piecewise `C¹` path `P` from `0` to `e₁`, and `φ` deviates by
  at most `θ` from `φ(s x)` on `cbox (s x) (3 s)`, then
  `∑_{x ∈ X} s e^{ξ φ(s x)} ≤ (4/7) 7^d e^{|ξ| θ} ∫_P e^{ξ φ} |dz|`.
  Proof: `P` passes within `(5/4) s` of `s x` and leaves `cbox (s x) (3 s)` (as
  `|e₁ - 0|_∞ = 1 > 6 s`), so (`exists_exit_cbox`) it spends a time interval inside the box along
  which its chord is `≥ (7/4) s`; there `φ ≥ φ(s x) - θ`; a point of `ℝ^d` lies in at most `7^d`
  of the boxes `cbox (s x) (3 s)`, `x ∈ ℤ^d` (`card_filter_mem_cbox_le`), and
  `sum_integral_le_of_overlap` sums the interval integrals with this multiplicity.
* `exists_coarsePath` (target T1): both statements for the near-geodesic of DGZ Step 2 at scale
  `s = 2^{-m}`, `m ≥ 3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Relation
open HigherDimLFPP.Perc (Zd LAdj SAdj WithinInf StepIn)

namespace HigherDimLFPP

namespace DGZ

variable {d : ℕ}

/-! ### Lattice points and `ℓ^∞` boxes -/

/-- The point `s x ∈ ℝ^d` of the lattice `s ℤ^d` with integer coordinates `x`. -/
def latPt (s : ℝ) (x : Zd d) : Rd d := WithLp.toLp 2 (fun i => s * (x i : ℝ))

theorem latPt_apply (s : ℝ) (x : Zd d) (i : Fin d) : latPt s x i = s * (x i : ℝ) := rfl

theorem latPt_zero (s : ℝ) : latPt s (0 : Zd d) = 0 := by
  ext i
  simp [latPt_apply]

/-- The integer point `N e₁ ∈ ℤ^d`. -/
def latE1 (d : ℕ) (N : ℤ) : Zd d := fun i => if (i : ℕ) = 0 then N else 0

theorem latPt_latE1 {s : ℝ} {N : ℤ} (h : s * N = 1) : latPt s (latE1 d N) = e₁ d := by
  ext i
  rw [latPt_apply, e₁_ofLp]
  simp only [latE1]
  split_ifs <;> simp [h]

/-- The closed `ℓ^∞` box `c + [-r, r]^d`. -/
def cbox (c : Rd d) (r : ℝ) : Set (Rd d) := {z | ∀ i, |z i - c i| ≤ r}

/-- The open `ℓ^∞` box `c + (-r, r)^d`. -/
def obox (c : Rd d) (r : ℝ) : Set (Rd d) := {z | ∀ i, |z i - c i| < r}

theorem obox_subset_cbox (c : Rd d) (r : ℝ) : obox c r ⊆ cbox c r :=
  fun _ hz i => (hz i).le

theorem mem_obox_self (c : Rd d) {r : ℝ} (hr : 0 < r) : c ∈ obox c r := fun i => by
  rw [sub_self, abs_zero]; exact hr

theorem isOpen_obox (c : Rd d) (r : ℝ) : IsOpen (obox c r) := by
  have : obox c r = ⋂ i : Fin d, {z : Rd d | |z i - c i| < r} := by
    ext z; simp only [obox, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_abs.comp ((PiLp.continuous_apply 2 _ i).sub continuous_const))
      continuous_const

theorem isClosed_cbox (c : Rd d) (r : ℝ) : IsClosed (cbox c r) := by
  have : cbox c r = ⋂ i : Fin d, {z : Rd d | |z i - c i| ≤ r} := by
    ext z; simp only [cbox, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_abs.comp ((PiLp.continuous_apply 2 _ i).sub continuous_const))
      continuous_const

theorem convex_obox (c : Rd d) (r : ℝ) : Convex ℝ (obox c r) := by
  intro z hz w hw a b ha hb hab i
  have e : (a • z + b • w) i - c i = a * (z i - c i) + b * (w i - c i) := by
    have : (a • z + b • w) i = a * z i + b * w i := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [this]
    have hc : c i = (a + b) * c i := by rw [hab, one_mul]
    linarith [hc]
  rw [e]
  rcases ha.lt_or_eq with ha' | ha'
  · calc |a * (z i - c i) + b * (w i - c i)| ≤ |a * (z i - c i)| + |b * (w i - c i)| :=
          abs_add_le _ _
      _ = a * |z i - c i| + b * |w i - c i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < a * r + b * r := by
          have h1 : a * |z i - c i| < a * r := mul_lt_mul_of_pos_left (hz i) ha'
          have h2 : b * |w i - c i| ≤ b * r := mul_le_mul_of_nonneg_left (hw i).le hb
          linarith
      _ = r := by rw [← add_mul, hab, one_mul]
  · subst ha'
    rw [zero_add] at hab
    subst hab
    simpa using hw i

/-- A coordinate is at most the Euclidean norm. -/
theorem abs_apply_le_norm (z : Rd d) (i : Fin d) : |z i| ≤ ‖z‖ := by
  have h := PiLp.norm_apply_le z i
  rwa [Real.norm_eq_abs] at h

/-! ### Rounding toward zero -/

/-- Rounding a real number toward `0` to an integer. -/
def truncZ (u : ℝ) : ℤ := if 0 ≤ u then ⌊u⌋ else ⌈u⌉

theorem truncZ_of_nonneg {u : ℝ} (h : 0 ≤ u) : truncZ u = ⌊u⌋ := by
  simp only [truncZ, h, ↓reduceIte]

theorem truncZ_of_neg {u : ℝ} (h : u < 0) : truncZ u = ⌈u⌉ := by
  simp only [truncZ, not_le.2 h, ↓reduceIte]

theorem truncZ_intCast (n : ℤ) : truncZ n = n := by
  by_cases h : (0 : ℝ) ≤ n
  · rw [truncZ_of_nonneg h, Int.floor_intCast]
  · rw [truncZ_of_neg (not_le.1 h), Int.ceil_intCast]

theorem truncZ_zero : truncZ 0 = 0 := by
  have := truncZ_intCast 0
  simpa using this

/-- Rounding toward `0` does not increase the absolute value. -/
theorem abs_truncZ_le (u : ℝ) : |(truncZ u : ℝ)| ≤ |u| := by
  by_cases h : 0 ≤ u
  · rw [truncZ_of_nonneg h, abs_of_nonneg h, abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.2 h)]
    exact Int.floor_le u
  · have h' : u < 0 := not_le.1 h
    rw [truncZ_of_neg h', abs_of_neg h']
    have h1 : (⌈u⌉ : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by exact_mod_cast h'.le)
    rw [abs_of_nonpos h1]
    linarith [Int.le_ceil u]

/-- Rounding toward `0` moves by less than `1`. -/
theorem abs_sub_truncZ_lt (u : ℝ) : |u - truncZ u| < 1 := by
  rw [abs_lt]
  by_cases h : 0 ≤ u
  · rw [truncZ_of_nonneg h]
    constructor <;> linarith [Int.floor_le u, Int.lt_floor_add_one u]
  · rw [truncZ_of_neg (not_le.1 h)]
    constructor <;> linarith [Int.le_ceil u, Int.ceil_lt_add_one u]

/-- Real numbers at distance `< 1` round toward `0` to integers at distance `≤ 1`. -/
theorem abs_truncZ_sub_truncZ_le_one {u v : ℝ} (h : |u - v| < 1) :
    |truncZ u - truncZ v| ≤ 1 := by
  rw [abs_lt] at h
  rw [abs_le]
  by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
  · rw [truncZ_of_nonneg hu, truncZ_of_nonneg hv]
    have h1 : (⌊u⌋ : ℝ) < ⌊v⌋ + 2 := by linarith [Int.floor_le u, Int.lt_floor_add_one v]
    have h2 : (⌊v⌋ : ℝ) < ⌊u⌋ + 2 := by linarith [Int.floor_le v, Int.lt_floor_add_one u]
    have h1' : ⌊u⌋ < ⌊v⌋ + 2 := by exact_mod_cast h1
    have h2' : ⌊v⌋ < ⌊u⌋ + 2 := by exact_mod_cast h2
    constructor <;> omega
  · have hv' : v < 0 := not_le.1 hv
    rw [truncZ_of_nonneg hu, truncZ_of_neg hv']
    have e1 : ⌊u⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hu, by linarith⟩
    have e2 : ⌈v⌉ = 0 := by
      rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith
    rw [e1, e2]; norm_num
  · have hu' : u < 0 := not_le.1 hu
    rw [truncZ_of_neg hu', truncZ_of_nonneg hv]
    have e1 : ⌊v⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hv, by linarith⟩
    have e2 : ⌈u⌉ = 0 := by
      rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith
    rw [e1, e2]; norm_num
  · have hu' : u < 0 := not_le.1 hu
    have hv' : v < 0 := not_le.1 hv
    rw [truncZ_of_neg hu', truncZ_of_neg hv']
    have h1 : (⌈u⌉ : ℝ) < ⌈v⌉ + 2 := by linarith [Int.le_ceil v, Int.ceil_lt_add_one u]
    have h2 : (⌈v⌉ : ℝ) < ⌈u⌉ + 2 := by linarith [Int.le_ceil u, Int.ceil_lt_add_one v]
    have h1' : ⌈u⌉ < ⌈v⌉ + 2 := by exact_mod_cast h1
    have h2' : ⌈v⌉ < ⌈u⌉ + 2 := by exact_mod_cast h2
    constructor <;> omega

/-- Rounding a point of `ℝ^d` toward `0` to the lattice `s ℤ^d` (coordinatewise). -/
def roundLat (s : ℝ) (z : Rd d) : Zd d := fun i => truncZ (z i / s)

theorem abs_latPt_roundLat_le {s : ℝ} (hs : 0 < s) (z : Rd d) (i : Fin d) :
    |latPt s (roundLat s z) i| ≤ |z i| := by
  rw [latPt_apply, abs_mul, abs_of_pos hs]
  calc s * |(truncZ (z i / s) : ℝ)| ≤ s * |z i / s| :=
        mul_le_mul_of_nonneg_left (abs_truncZ_le _) hs.le
    _ = |z i| := by rw [abs_div, abs_of_pos hs]; field_simp

theorem abs_latPt_roundLat_sub_lt {s : ℝ} (hs : 0 < s) (z : Rd d) (i : Fin d) :
    |latPt s (roundLat s z) i - z i| < s := by
  rw [latPt_apply]
  have e : s * (roundLat s z i : ℝ) - z i = -(s * (z i / s - truncZ (z i / s))) := by
    simp only [roundLat]; field_simp; ring
  rw [e, abs_neg, abs_mul, abs_of_pos hs]
  calc s * |z i / s - truncZ (z i / s)| < s * 1 :=
        mul_lt_mul_of_pos_left (abs_sub_truncZ_lt _) hs
    _ = s := mul_one s

theorem withinInf_roundLat {s : ℝ} (hs : 0 < s) {z w : Rd d} (h : ∀ i, |z i - w i| < s) :
    WithinInf 1 (roundLat s z) (roundLat s w) := fun i => by
  refine abs_truncZ_sub_truncZ_le_one ?_
  rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs]
  exact h i

theorem roundLat_zero (s : ℝ) : roundLat s (0 : Rd d) = 0 := by
  funext i
  simp only [roundLat]
  rw [show (0 : Rd d) i = 0 from rfl, zero_div, truncZ_zero]
  rfl

theorem roundLat_e₁ {s : ℝ} (hs : 0 < s) {N : ℤ} (h : s * N = 1) :
    roundLat s (e₁ d) = latE1 d N := by
  funext i
  simp only [roundLat, latE1]
  rw [e₁_ofLp]
  split_ifs
  · have : (1 : ℝ) / s = N := by
      field_simp; linarith
    rw [this, truncZ_intCast]
  · rw [zero_div, truncZ_zero]

/-! ### Loop erasure -/

/-- **Loop erasure**: an L-path inside `S` from a site `a ∈ S` to `b` contains a duplicate-free
L-path inside `S` with the same endpoints (via `SimpleGraph.Walk.bypass`). -/
theorem exists_nodup_isChain_of_reflTransGen {S : Set (Zd d)} {a b : Zd d} (ha : a ∈ S)
    (h : ReflTransGen (StepIn S LAdj) a b) :
    ∃ l : List (Zd d), l.Nodup ∧ l.IsChain LAdj ∧ l.head? = some a ∧ l.getLast? = some b ∧
      ∀ y ∈ l, y ∈ S := by
  classical
  set G : SimpleGraph (Zd d) := SimpleGraph.fromRel (StepIn S LAdj) with hG
  have hGadj : ∀ {x y}, G.Adj x y → LAdj x y ∧ x ∈ S ∧ y ∈ S := by
    intro x y hxy
    rw [hG, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with h' | h'
    · exact ⟨h'.2.2, h'.1, h'.2.1⟩
    · exact ⟨h'.2.2.symm, h'.2.1, h'.1⟩
  have hreach : G.Reachable a b := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    refine ReflTransGen.mono (fun x y (hxy : StepIn S LAdj x y) => ?_) a b h
    rw [hG, SimpleGraph.fromRel_adj]
    exact ⟨hxy.2.2.ne, Or.inl hxy⟩
  obtain ⟨p⟩ := hreach
  set q := p.bypass with hq
  refine ⟨q.support, p.bypass_isPath.support_nodup,
    q.isChain_adj_support.imp fun _ _ h => (hGadj h).1, ?_, ?_, ?_⟩
  · rw [← q.cons_tail_support]; rfl
  · rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  · exact Perc.walk_support_forall (fun h => ⟨(hGadj h).2.1, (hGadj h).2.2⟩) q ha

/-! ### D8: discretization of a continuous path -/

/-- **HA5 D8** (DGZ Lemma 3.3, Step 2, (3.19), corrected as in HA5 finding G2). Let `s > 0` with
`s N = 1` (`N ∈ ℤ`) and let `P : [0,1] → U = (-2,2)^d` be continuous with `P 0 = 0`, `P 1 = e₁`.
Then there are distinct sites `x₁ = 0, …, x_J = N e₁` of `ℤ^d`, consecutive ones L-adjacent (so
`|s x_j - s x_{j+1}|₁ = s`), with `s x_j ∈ U` and `|s x_j - P(t_j)|_∞ < (5/4) s` for some
`t_j ∈ [0,1]`. -/
theorem exists_latticePath {s : ℝ} (hs : 0 < s) {N : ℤ} (hsN : s * N = 1) {P : ℝ → Rd d}
    (hPc : ContinuousOn P (Icc 0 1)) (hPU : MapsTo P (Icc 0 1) (cube d)) (hP0 : P 0 = 0)
    (hP1 : P 1 = e₁ d) :
    ∃ l : List (Zd d), l.Nodup ∧ l.IsChain LAdj ∧ l.head? = some 0 ∧
      l.getLast? = some (latE1 d N) ∧
      ∀ x ∈ l, latPt s x ∈ cube d ∧
        ∃ t ∈ Icc (0 : ℝ) 1, ∀ i, |latPt s x i - P t i| < 5 / 4 * s := by
  -- uniform continuity of `P` on `[0,1]`
  obtain ⟨δ, hδ, hPδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hPc) (s / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set M : ℕ := n + 1 with hM
  have hMpos : (0 : ℝ) < M := by positivity
  set t : ℕ → ℝ := fun j => (j : ℝ) / M with ht
  have ht_mem : ∀ j ≤ M, t j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨div_nonneg (Nat.cast_nonneg j) hMpos.le, (div_le_one hMpos).2 ?_⟩
    exact_mod_cast hj
  have hclose : ∀ j < M, ∀ i, |P (t (j + 1)) i - P (t j) i| < s / 4 := by
    intro j hj i
    have hd' : dist (t (j + 1)) (t j) < δ := by
      rw [Real.dist_eq, ht]
      have e : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = 1 / ((n : ℝ) + 1) := by
        rw [← sub_div]; push_cast; rw [hM]; push_cast; ring
      rw [e, abs_of_pos (by positivity)]
      exact hn
    have h1 := hPδ _ (ht_mem (j + 1) hj) _ (ht_mem j hj.le) hd'
    rw [dist_eq_norm] at h1
    have h2 := abs_apply_le_norm (P (t (j + 1)) - P (t j)) i
    rw [PiLp.sub_apply] at h2
    linarith
  set z : ℕ → Zd d := fun j => roundLat s (P (t j)) with hz
  set G : Set (Zd d) := {w | latPt s w ∈ cube d ∧
    ∃ τ ∈ Icc (0 : ℝ) 1, ∀ i, |latPt s w i - P τ i| < 5 / 4 * s} with hG
  have hzU : ∀ j ≤ M, ∀ i, |latPt s (z j) i| < 2 := fun j hj i =>
    (abs_latPt_roundLat_le hs _ i).trans_lt (hPU (ht_mem j hj) i)
  have hstep : ∀ j < M, ReflTransGen (StepIn G LAdj) (z j) (z (j + 1)) := by
    intro j hj
    have hW : WithinInf 1 (z j) (z (j + 1)) :=
      withinInf_roundLat hs fun i => by
        rw [abs_sub_comm]; linarith [hclose j hj i]
    refine Perc.reflTransGen_stepIn_mono (fun w hw => ?_) (Perc.reflTransGen_cube hW)
    refine ⟨fun i => ?_, t j, ht_mem j hj.le, fun i => ?_⟩
    · rcases hw i with h | h
      · rw [latPt_apply, h, ← latPt_apply]; exact hzU j hj.le i
      · rw [latPt_apply, h, ← latPt_apply]; exact hzU (j + 1) hj i
    · rcases hw i with h | h
      · rw [latPt_apply, h, ← latPt_apply]
        linarith [abs_latPt_roundLat_sub_lt hs (P (t j)) i]
      · rw [latPt_apply, h, ← latPt_apply]
        have h1 := abs_latPt_roundLat_sub_lt hs (P (t (j + 1))) i
        have h2 := hclose j hj i
        calc |latPt s (z (j + 1)) i - P (t j) i|
            = |(latPt s (z (j + 1)) i - P (t (j + 1)) i) + (P (t (j + 1)) i - P (t j) i)| := by
              ring_nf
          _ ≤ |latPt s (z (j + 1)) i - P (t (j + 1)) i| + |P (t (j + 1)) i - P (t j) i| :=
              abs_add_le _ _
          _ < s + s / 4 := add_lt_add h1 h2
          _ = 5 / 4 * s := by ring
  have hchain : ∀ j ≤ M, ReflTransGen (StepIn G LAdj) (z 0) (z j) := by
    intro j hj
    induction j with
    | zero => exact ReflTransGen.refl
    | succ j ih => exact (ih (Nat.le_of_succ_le hj)).trans (hstep j (Nat.lt_of_succ_le hj))
  have ht0 : t 0 = 0 := by simp [ht]
  have htM : t M = 1 := by
    simp only [ht]; exact div_self hMpos.ne'
  have hz0 : z 0 = 0 := by simp only [hz, ht0, hP0, roundLat_zero]
  have hzM : z M = latE1 d N := by simp only [hz, htM, hP1, roundLat_e₁ hs hsN]
  have h0G : (0 : Zd d) ∈ G := by
    refine ⟨by rw [latPt_zero]; exact zero_mem_cube d, 0, ⟨le_rfl, zero_le_one⟩, fun i => ?_⟩
    rw [latPt_zero, hP0, sub_self]
    show |(0 : ℝ)| < 5 / 4 * s
    rw [abs_zero]; positivity
  have hfinal := hchain M le_rfl
  rw [hz0, hzM] at hfinal
  obtain ⟨l, hnd, hch, hh, hl, hS⟩ := exists_nodup_isChain_of_reflTransGen h0G hfinal
  exact ⟨l, hnd, hch, hh, hl, hS⟩

/-! ### Exit from a box -/

/-- **Exit from a closed box, forward.** If `g` is continuous on `[a₀, b₀]`, `g a₀` lies within
`ℓ^∞`-distance `r₁` of `c` and `g b₀ ∉ cbox c r₂` with `r₁ < r₂`, then for the first exit time `τ`
the path stays in `cbox c r₂` on `[a₀, τ]` and some coordinate moved by at least `r₂ - r₁`. -/
theorem exists_exit_cbox {g : ℝ → Rd d} {a₀ b₀ : ℝ} (hab : a₀ ≤ b₀)
    (hg : ContinuousOn g (Icc a₀ b₀)) {c : Rd d} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (ha : ∀ i, |g a₀ i - c i| ≤ r₁) (hb : g b₀ ∉ cbox c r₂) :
    ∃ τ ∈ Icc a₀ b₀, (∀ t ∈ Icc a₀ τ, g t ∈ cbox c r₂) ∧ ∃ i, r₂ - r₁ ≤ |g τ i - g a₀ i| := by
  have hcoord : ∀ i, ContinuousOn (fun t => |g t i - c i|) (Icc a₀ b₀) := fun i =>
    continuous_abs.comp_continuousOn
      (((PiLp.continuous_apply 2 _ i).comp_continuousOn hg).sub continuousOn_const)
  set S : Set ℝ := ⋃ i : Fin d, Icc a₀ b₀ ∩ (fun t => |g t i - c i|) ⁻¹' Ici r₂ with hS
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun i =>
    (hcoord i).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hbS : b₀ ∈ S := by
    simp only [cbox, mem_ofPred_eq, not_forall, not_le] at hb
    obtain ⟨i, hi⟩ := hb
    exact mem_iUnion.2 ⟨i, ⟨hab, le_rfl⟩, hi.le⟩
  have hSb : BddBelow S := ⟨a₀, fun t ht => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 ht
    exact hi.1.1⟩
  set τ := sInf S with hτ
  have hτS : τ ∈ S := hSc.csInf_mem ⟨b₀, hbS⟩ hSb
  obtain ⟨i₀, hτIcc, hτi⟩ : ∃ i, τ ∈ Icc a₀ b₀ ∧ r₂ ≤ |g τ i - c i| := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hτS
    exact ⟨i, hi.1, hi.2⟩
  have hlt : ∀ t ∈ Ico a₀ τ, ∀ i, |g t i - c i| < r₂ := by
    intro t ht i
    by_contra hcon
    have htS : t ∈ S := mem_iUnion.2 ⟨i, ⟨ht.1, ht.2.le.trans hτIcc.2⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hSb htS) (not_le.2 ht.2)
  have hτpos : a₀ < τ := by
    rcases hτIcc.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hτi
      linarith [ha i₀]
  have hbox : ∀ t ∈ Icc a₀ τ, g t ∈ cbox c r₂ := by
    intro t ht
    rcases ht.2.lt_or_eq with h | h
    · exact fun i => (hlt t ⟨ht.1, h⟩ i).le
    · have hcw : ContinuousWithinAt g (Ico a₀ τ) τ :=
        (hg τ hτIcc).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτIcc.2))
      have hmem := hcw.mem_closure_image (by
        rw [closure_Ico hτpos.ne]; exact right_mem_Icc.2 hτIcc.1)
      have hsub : g '' Ico a₀ τ ⊆ cbox c r₂ := by
        rintro _ ⟨u, hu, rfl⟩
        exact fun i => (hlt u hu i).le
      rw [h]
      exact (isClosed_cbox c r₂).closure_subset_iff.2 hsub hmem
  refine ⟨τ, hτIcc, hbox, i₀, ?_⟩
  have h1 := ha i₀
  have h2 := abs_sub_abs_le_abs_sub (g τ i₀ - c i₀) (g a₀ i₀ - c i₀)
  rw [sub_sub_sub_cancel_right] at h2
  linarith

/-- **Exit from a closed box, backward.** If `g b₀` lies within `r₁` of `c` and
`g a₀ ∉ cbox c r₂`, `r₁ < r₂`, then for some `τ ∈ [a₀, b₀]` the path stays in `cbox c r₂` on
`[τ, b₀]` and some coordinate of `g b₀ - g τ` is at least `r₂ - r₁` in absolute value. -/
theorem exists_exit_cbox_rev {g : ℝ → Rd d} {a₀ b₀ : ℝ} (hab : a₀ ≤ b₀)
    (hg : ContinuousOn g (Icc a₀ b₀)) {c : Rd d} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (hb : ∀ i, |g b₀ i - c i| ≤ r₁) (ha : g a₀ ∉ cbox c r₂) :
    ∃ τ ∈ Icc a₀ b₀, (∀ t ∈ Icc τ b₀, g t ∈ cbox c r₂) ∧ ∃ i, r₂ - r₁ ≤ |g b₀ i - g τ i| := by
  set g' : ℝ → Rd d := fun t => g (a₀ + b₀ - t) with hg'
  have hmaps : MapsTo (fun t : ℝ => a₀ + b₀ - t) (Icc a₀ b₀) (Icc a₀ b₀) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hg'c : ContinuousOn g' (Icc a₀ b₀) :=
    hg.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have e1 : g' a₀ = g b₀ := by simp only [hg', add_sub_cancel_left]
  have e2 : g' b₀ = g a₀ := by simp only [hg', add_sub_cancel_right]
  obtain ⟨τ', hτ', hbox, i, hi⟩ :=
    exists_exit_cbox hab hg'c hr (by rw [e1]; exact hb) (by rw [e2]; exact ha)
  refine ⟨a₀ + b₀ - τ', ⟨by linarith [hτ'.2], by linarith [hτ'.1]⟩, fun t ht => ?_, i, ?_⟩
  · have h := hbox (a₀ + b₀ - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [hg', sub_sub_cancel] at h
    exact h
  · rw [e1] at hi
    rw [abs_sub_comm]
    exact hi

/-! ### Overlap counting -/

/-- **Sum of interval integrals with bounded overlap**: if the intervals `[a x, b x] ⊆ [0,1]`,
`x ∈ X`, cover every time at most `K` times and `f ≥ 0` is integrable on `[0,1]`, then
`∑ₓ ∫_{a x}^{b x} f ≤ K ∫₀¹ f`. -/
theorem sum_integral_le_of_overlap {ι : Type*} (X : Finset ι) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) (a b : ι → ℝ)
    (hab : ∀ x ∈ X, 0 ≤ a x ∧ a x ≤ b x ∧ b x ≤ 1) {K : ℕ}
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (X.filter fun x => t ∈ Icc (a x) (b x)).card ≤ K) :
    ∑ x ∈ X, ∫ t in a x..b x, f t ≤ K * ∫ t in (0 : ℝ)..1, f t := by
  classical
  have hfI : IntegrableOn f (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hf
  have h1 : ∀ x ∈ X, ∫ t in a x..b x, f t =
      ∫ t in Ioc (0 : ℝ) 1, (Ioc (a x) (b x)).indicator f t := by
    intro x hx
    obtain ⟨h0a, hab', hb1⟩ := hab x hx
    rw [intervalIntegral.integral_of_le hab', integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 (Ioc_subset_Ioc h0a hb1)]
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ fun x _ =>
    hfI.indicator measurableSet_Ioc, intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul]
  refine setIntegral_mono_on (integrable_finsetSum _ fun x _ => hfI.indicator measurableSet_Ioc)
    (hfI.const_mul _) measurableSet_Ioc fun t ht => ?_
  have hsum : ∑ x ∈ X, (Ioc (a x) (b x)).indicator f t =
      ((X.filter fun x => t ∈ Ioc (a x) (b x)).card : ℝ) * f t := by
    simp only [Set.indicator_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hcard : (X.filter fun x => t ∈ Ioc (a x) (b x)).card ≤ K := by
    refine le_trans (Finset.card_le_card fun x hx => ?_) (hK t (Ioc_subset_Icc_self ht))
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, Ioc_subset_Icc_self hx.2⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf0 t (Ioc_subset_Icc_self ht))

open Classical in
/-- A point of `ℝ^d` lies in at most `7^d` of the boxes `cbox (s x) (3 s)`, `x ∈ ℤ^d`. -/
theorem card_filter_mem_cbox_le {s : ℝ} (hs : 0 < s) (X : Finset (Zd d)) (p : Rd d) :
    (X.filter fun x => p ∈ cbox (latPt s x) (3 * s)).card ≤ 7 ^ d := by
  set q : Zd d := fun i => round (p i / s) with hq
  have hsub : X.filter (fun x => p ∈ cbox (latPt s x) (3 * s)) ⊆ Perc.boxF q 3 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Perc.mem_boxF]
    intro i
    have h1 := hx.2 i
    rw [latPt_apply] at h1
    have h2 : |p i / s - x i| ≤ 3 := by
      have e : p i / s - x i = (p i - s * x i) / s := by field_simp
      rw [e, abs_div, abs_of_pos hs, div_le_iff₀ hs]
      linarith
    have h3 := abs_sub_round (p i / s)
    have h4 : |((x i - q i : ℤ) : ℝ)| < 4 := by
      push_cast
      have e : (x i : ℝ) - (q i : ℝ) = -((p i / s - x i) - (p i / s - round (p i / s))) := by
        simp only [hq]; ring
      rw [e, abs_neg]
      calc |(p i / s - x i) - (p i / s - round (p i / s))|
          ≤ |p i / s - x i| + |p i / s - round (p i / s)| := abs_sub _ _
        _ < 4 := by linarith
    have h5 : |x i - q i| < 4 := by exact_mod_cast h4
    rw [abs_lt] at h5
    rw [abs_le]
    push_cast
    constructor <;> omega
  calc (X.filter fun x => p ∈ cbox (latPt s x) (3 * s)).card ≤ (Perc.boxF q 3).card :=
        Finset.card_le_card hsub
    _ = 7 ^ d := by rw [Perc.card_boxF]

/-! ### (3.20′): the weighted sum over the discretized path -/

/-- A path from `0` to `e₁` does not stay in a closed box of radius `3 s` when `6 s < 1`
(`d ≥ 1`): one of its endpoints lies outside. -/
theorem not_mem_cbox_zero_or_e₁ (hd : 0 < d) {s : ℝ} (hs6 : 6 * s < 1) (c : Rd d) :
    (0 : Rd d) ∉ cbox c (3 * s) ∨ e₁ d ∉ cbox c (3 * s) := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h0, h1⟩ := hcon
  have h0' := h0 ⟨0, hd⟩
  have h1' := h1 ⟨0, hd⟩
  have e0 : (0 : Rd d) ⟨0, hd⟩ = 0 := rfl
  have e1 : (e₁ d) ⟨0, hd⟩ = 1 := by rw [e₁_ofLp]; simp
  rw [e0] at h0'
  rw [e1] at h1'
  have h2 := abs_sub_le (1 : ℝ) (c ⟨0, hd⟩) 0
  rw [abs_sub_comm (c ⟨0, hd⟩) 0, sub_zero, abs_one] at h2
  linarith

/-- **(3.20′)** (HA5, "Use (DGZ (3.20))"). Let `s > 0` with `6 s < 1`, `d ≥ 1`, `φ` continuous,
`P` a piecewise `C¹` path from `0` to `e₁`, and `X` a finite set of sites such that every `s x`,
`x ∈ X`, is within `ℓ^∞`-distance `(5/4) s` of some point of `P`, and `|φ - φ(s x)| ≤ θ` on
`cbox (s x) (3 s)`. Then `∑_{x ∈ X} s e^{ξ φ(s x)} ≤ (4/7) 7^d e^{|ξ| θ} ∫_P e^{ξ φ} |dz|`. -/
theorem sum_mul_exp_le (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs6 : 6 * s < 1) {ξ θ : ℝ}
    {φ : Rd d → ℝ} (hφ : Continuous φ) {P : ℝ → Rd d} (hP : IsPcwC1Path P 0 (e₁ d))
    (X : Finset (Zd d))
    (hnear : ∀ x ∈ X, ∃ t ∈ Icc (0 : ℝ) 1, ∀ i, |latPt s x i - P t i| < 5 / 4 * s)
    (hosc : ∀ x ∈ X, ∀ z ∈ cbox (latPt s x) (3 * s), |φ z - φ (latPt s x)| ≤ θ) :
    ∑ x ∈ X, s * Real.exp (ξ * φ (latPt s x)) ≤
      4 / 7 * 7 ^ d * Real.exp (|ξ| * θ) * lfppLength ξ φ P := by
  classical
  have hr : 5 / 4 * s < 3 * s := by linarith
  -- every site gets a time interval inside its box along which the chord is `≥ (7/4) s`
  have hint : ∀ x ∈ X, ∃ a b : ℝ, (0 ≤ a ∧ a ≤ b ∧ b ≤ 1) ∧
      (∀ t ∈ Icc a b, P t ∈ cbox (latPt s x) (3 * s)) ∧ 7 / 4 * s ≤ ‖P b - P a‖ := by
    intro x hx
    obtain ⟨t₀, ht₀, hnear₀⟩ := hnear x hx
    have hnear' : ∀ i, |P t₀ i - latPt s x i| ≤ 5 / 4 * s := fun i => by
      rw [abs_sub_comm]; exact (hnear₀ i).le
    rcases not_mem_cbox_zero_or_e₁ hd hs6 (latPt s x) with h0 | h1
    · rw [← hP.source] at h0
      obtain ⟨τ, hτ, hbox, i, hi⟩ := exists_exit_cbox_rev ht₀.1
        (hP.continuousOn.mono (Icc_subset_Icc le_rfl ht₀.2)) hr hnear' h0
      refine ⟨τ, t₀, ⟨hτ.1, hτ.2, ht₀.2⟩, hbox, ?_⟩
      have h2 := abs_apply_le_norm (P t₀ - P τ) i
      rw [PiLp.sub_apply] at h2
      linarith
    · rw [← hP.target] at h1
      obtain ⟨τ, hτ, hbox, i, hi⟩ := exists_exit_cbox ht₀.2
        (hP.continuousOn.mono (Icc_subset_Icc ht₀.1 le_rfl)) hr hnear' h1
      refine ⟨t₀, τ, ⟨ht₀.1, hτ.1, hτ.2⟩, hbox, ?_⟩
      have h2 := abs_apply_le_norm (P τ - P t₀) i
      rw [PiLp.sub_apply] at h2
      linarith
  choose! a b hab hbox hchord using hint
  -- the lower bound on each interval
  have hlow : ∀ x ∈ X, s * Real.exp (ξ * φ (latPt s x)) ≤
      4 / 7 * Real.exp (|ξ| * θ) * ∫ t in a x..b x, lfppIntegrand ξ φ P t := by
    intro x hx
    obtain ⟨h0a, hab', hb1⟩ := hab x hx
    have hm : ∀ t ∈ Icc (a x) (b x), ξ * φ (latPt s x) - |ξ| * θ ≤ ξ * φ (P t) := by
      intro t ht
      have h1 := hosc x hx (P t) (hbox x hx t ht)
      have h2 : |ξ * φ (P t) - ξ * φ (latPt s x)| ≤ |ξ| * θ := by
        rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg ξ)
      linarith [neg_abs_le (ξ * φ (P t) - ξ * φ (latPt s x))]
    have hI := hP.exp_mul_norm_sub_le_integral hφ h0a hab' hb1 hm
    have hE : 0 < Real.exp (ξ * φ (latPt s x) - |ξ| * θ) := Real.exp_pos _
    have h3 : Real.exp (ξ * φ (latPt s x) - |ξ| * θ) * (7 / 4 * s) ≤
        ∫ t in a x..b x, lfppIntegrand ξ φ P t :=
      (mul_le_mul_of_nonneg_left (hchord x hx) hE.le).trans hI
    have e : s * Real.exp (ξ * φ (latPt s x)) = 4 / 7 * Real.exp (|ξ| * θ) *
        (Real.exp (ξ * φ (latPt s x) - |ξ| * θ) * (7 / 4 * s)) := by
      have : Real.exp (ξ * φ (latPt s x)) =
          Real.exp (|ξ| * θ) * Real.exp (ξ * φ (latPt s x) - |ξ| * θ) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  -- overlap: every time lies in at most `7^d` of the intervals
  have hK : ∀ t ∈ Icc (0 : ℝ) 1, (X.filter fun x => t ∈ Icc (a x) (b x)).card ≤ 7 ^ d := by
    intro t _
    refine le_trans (Finset.card_le_card fun x hx => ?_) (card_filter_mem_cbox_le hs X (P t))
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hbox x hx.1 t hx.2⟩
  have hover := sum_integral_le_of_overlap X (hP.intervalIntegrable_lfppIntegrand hφ ξ)
    (fun t _ => lfppIntegrand_nonneg ξ φ P t) a b hab hK
  calc ∑ x ∈ X, s * Real.exp (ξ * φ (latPt s x))
      ≤ ∑ x ∈ X, 4 / 7 * Real.exp (|ξ| * θ) * ∫ t in a x..b x, lfppIntegrand ξ φ P t :=
        Finset.sum_le_sum hlow
    _ = 4 / 7 * Real.exp (|ξ| * θ) * ∑ x ∈ X, ∫ t in a x..b x, lfppIntegrand ξ φ P t := by
        rw [Finset.mul_sum]
    _ ≤ 4 / 7 * Real.exp (|ξ| * θ) *
          (((7 ^ d : ℕ) : ℝ) * ∫ t in (0 : ℝ)..1, lfppIntegrand ξ φ P t) :=
        mul_le_mul_of_nonneg_left hover (by positivity)
    _ = 4 / 7 * 7 ^ d * Real.exp (|ξ| * θ) * lfppLength ξ φ P := by
        rw [lfppLength_eq_integral]; push_cast; ring

/-! ### Target T1 -/

/-- **Target T1** (HA5 D8 and (3.20′) at scale `2^{-m}`, DGZ Lemma 3.3, Step 2). Let `d ≥ 1`,
`m ≥ 3`, `s = 2^{-m}`, `φ` continuous, and `P` an admissible path (piecewise `C¹`, `[0,1] → U`, from
`0` to `e₁`). Then there are distinct sites `x₁ = 0, …, x_J = 2^m e₁` (as a list), consecutive ones
L-adjacent, with `s x_j ∈ U` and `|s x_j - P(t_j)|_∞ < (5/4) s`; and if `|φ - φ(s x)| ≤ θ` on
`cbox (s x) (3 s)` for every site with `s x ∈ U` (the oscillation event of DGZ Step 1), then
`∑_j s e^{ξ φ(s x_j)} ≤ (4/7) 7^d e^{|ξ| θ} ∫_P e^{ξ φ} |dz|`. -/
theorem exists_coarsePath (hd : 0 < d) {m : ℕ} (hm : 3 ≤ m) {ξ θ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) {P : ℝ → Rd d} (hP : IsAdmissiblePath d P)
    (hosc : ∀ x : Zd d, latPt ((2 : ℝ)⁻¹ ^ m) x ∈ cube d →
      ∀ z ∈ cbox (latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * (2 : ℝ)⁻¹ ^ m),
        |φ z - φ (latPt ((2 : ℝ)⁻¹ ^ m) x)| ≤ θ) :
    ∃ l : List (Zd d), l.Nodup ∧ l.IsChain LAdj ∧ l.head? = some 0 ∧
      l.getLast? = some (latE1 d (2 ^ m)) ∧
      (∀ x ∈ l, latPt ((2 : ℝ)⁻¹ ^ m) x ∈ cube d ∧
        ∃ t ∈ Icc (0 : ℝ) 1, ∀ i, |latPt ((2 : ℝ)⁻¹ ^ m) x i - P t i| < 5 / 4 * (2 : ℝ)⁻¹ ^ m) ∧
      ∑ x ∈ l.toFinset, (2 : ℝ)⁻¹ ^ m * Real.exp (ξ * φ (latPt ((2 : ℝ)⁻¹ ^ m) x)) ≤
        4 / 7 * 7 ^ d * Real.exp (|ξ| * θ) * lfppLength ξ φ P := by
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have hsN : (2 : ℝ)⁻¹ ^ m * (((2 : ℤ) ^ m : ℤ) : ℝ) = 1 := by
    push_cast; rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hs6 : 6 * (2 : ℝ)⁻¹ ^ m < 1 := by
    have h8 : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    norm_num at h8 ⊢
    linarith
  have hPa := isAdmissiblePath_iff.1 hP
  obtain ⟨l, hnd, hch, hh, hl, hS⟩ := exists_latticePath hs hsN hPa.1.continuousOn hPa.2
    hPa.1.source hPa.1.target
  refine ⟨l, hnd, hch, hh, hl, hS, ?_⟩
  refine sum_mul_exp_le hd hs hs6 hφ hPa.1 l.toFinset (fun x hx => (hS x
    (List.mem_toFinset.1 hx)).2) fun x hx => ?_
  exact hosc x (hS x (List.mem_toFinset.1 hx)).1

end DGZ

end HigherDimLFPP
