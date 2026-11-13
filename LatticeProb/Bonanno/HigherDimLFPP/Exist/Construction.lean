/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Construction at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Discretize
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Compare
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The deterministic construction of DGZ Lemma 3.3 (packet P-X7a, target T2)

Source: DGZ arXiv:2310.03996, proof of Lemma 3.3, Steps 2–4; planning audit HA5, finding G1 (the
"duality" of Step 3 is replaced by the surgery lemma), finding G3 (inner margin) and Details D9,
"Construction on E", steps (1)–(4).

Scales: the coarse lattice `2^{-m} ℤ^d` (sites `x`, points `s x`, `s = 2^{-m}`) and the fine lattice
`2^{-m-k} ℤ^d` (sites `y`, points `s' y`, `s' = 2^{-m-k}`); the coarse site `x` is the fine site
`2^k x` (`scaleSite`). The field is `φ = φ₀ + φ₁ + φ₂` with `φ₀` the coarse field (DGZ's `h_{0,m}`),
`φ₁` the middle band (`h_{m,m+k}`) and `φ₂` the fine band (`h_{m+k,n}`). A fine site `y` is *open*
(for the threshold `b`) if for every L-neighbour `y'` the internal distance of `φ₂` from `s' y` to
`s' y'` inside the open box `obox (s' y) (2 s')` is at most `s' b` (HA5 D9; sites outside the region
`|s' y|_∞ ≤ 2 - 2^{-m-3}` may be declared open, only the open sites of the region are used).

The good event of HA5 D9 is encoded as the hypotheses:
* `E₁`: `|φ₀ - φ₀(s x)| ≤ θ` on `cbox (s x) (3 s)` for every coarse site with `s x ∈ U`, and
  `φ₁ ≤ S` on `U`;
* `E₂`: an admissible path `P` with `∫_P e^{ξ φ₀} ≤ 2a`;
* `E₃ₐ`: every closed cluster meeting `B̄_{2^{m+k+1}}(0)` (fine lattice) has `ℓ^∞`-diameter
  `≤ 2^{k-2}`;
* `E₃ᵦ`: the fine sites `0` and `2^{m+k} e₁` are open and not enclosed by a closed cluster.

Main results (namespace `HigherDimLFPP.DGZ`):

* `exists_finePath` (steps (2)–(3)): the fine reference path through the scaled coarse sites, then
  the surgery lemma `Perc.surgeryLemma` (HA5 D7(iii)) with `D = 2^{k-2}` and `R = 2^{m+k+1}`, and
  loop erasure: distinct open fine sites `y₁ = 0, …, y_K = 2^{m+k} e₁`, consecutive ones
  L-adjacent, each within `14 · 2^{k-4}` fine steps (`≤ (7/8) 2^{-m}`) of a scaled coarse site.
* `lfppDistance_le_of_finePath` (step (4)): the chain bound `D ≤ ∑ᵢ D_{W_i}(s' y_i, s' y_{i+1})`
  (`lfppDistOn_le_sum`), the weight comparison on each box (`lfppDistOn_le_mul_of_exp_le`) and the
  count of fine sites per coarse site (`sum_comp_le`).
* `lfppDistance_le_of_good` (**target T2**): on the good event,
  `D^ξ(φ₀ + φ₁ + φ₂) ≤ (8/7) 7^d ((2^{k+1}+1)^d / 2^k) e^{2ξθ + ξS} a b`.
* `lfppDistance_le_of_good_exp` (target T2 with DGZ's parameters `θ = n^{2/3}`,
  `k = ⌊(log m)²⌋`, `8 ≤ m ≤ n`): `D^ξ(φ₀ + φ₁ + φ₂) ≤ e^{(14 d + 1 + 2ξ) n^{2/3} + ξ S} a b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Relation
open HigherDimLFPP.Perc (Zd LAdj SAdj WithinInf StepIn IsClosedCluster Encloses Ext)

namespace HigherDimLFPP

namespace DGZ

variable {d : ℕ}

/-! ### Scaled sites and the fine reference path -/

/-- The site `L x`: the coarse site `x` seen in the lattice that is `L` times finer. -/
def scaleSite (L : ℤ) (x : Zd d) : Zd d := fun i => L * x i

theorem scaleSite_apply (L : ℤ) (x : Zd d) (i : Fin d) : scaleSite L x i = L * x i := rfl

theorem scaleSite_zero (L : ℤ) : scaleSite L (0 : Zd d) = 0 := by
  funext i; simp [scaleSite]

theorem scaleSite_latE1 (L N : ℤ) : scaleSite L (latE1 d N) = latE1 d (L * N) := by
  funext i; simp only [scaleSite, latE1]; split_ifs <;> simp

/-- One coarse step, refined: if `x, x'` are L-adjacent, the sites `2h x` and `2h x'` are joined by
the straight L-path of `2h` fine steps, each site of which lies within `ℓ^∞`-distance `h` of
`2h x` or of `2h x'`. -/
theorem reflTransGen_scaleSite_of_lAdj (h : ℕ) {x x' : Zd d} (hxx' : LAdj x x') :
    ReflTransGen (StepIn {y | WithinInf (h : ℤ) y (scaleSite (2 * h) x) ∨
      WithinInf (h : ℤ) y (scaleSite (2 * h) x')} LAdj)
      (scaleSite (2 * h) x) (scaleSite (2 * h) x') := by
  -- the step from `2h z` to `2h (z + e_i)`
  have key : ∀ (z : Zd d) (i : Fin d), ReflTransGen (StepIn {y | WithinInf (h : ℤ) y
      (scaleSite (2 * h) z) ∨ WithinInf (h : ℤ) y (scaleSite (2 * h) (z + Pi.single i 1))} LAdj)
      (scaleSite (2 * h) z) (scaleSite (2 * h) (z + Pi.single i 1)) := by
    intro z i
    have e : scaleSite (2 * h) (z + Pi.single i 1) =
        scaleSite (2 * h) z + Pi.single i ((2 * h : ℕ) : ℤ) := by
      funext k
      simp only [scaleSite_apply, Perc.add_single_apply]
      split_ifs <;> push_cast <;> ring
    rw [e]
    refine Perc.reflTransGen_add_single_nat _ i (2 * h) fun t ht => ?_
    by_cases hth : t ≤ h
    · left
      intro k
      rw [Perc.add_single_apply]
      split_ifs
      · rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]; exact_mod_cast hth
      · rw [sub_self, abs_zero]; positivity
    · right
      intro k
      rw [Perc.add_single_apply, Perc.add_single_apply]
      split_ifs
      · rw [add_sub_add_left_eq_sub, abs_le]
        push_cast
        constructor <;> omega
      · rw [sub_self, abs_zero]; positivity
  obtain ⟨i, hi | hi⟩ := hxx'.exists_eq_add_single
  · subst hi; exact key x i
  · subst hi
    refine Perc.reflTransGen_lAdj_symm (Perc.reflTransGen_stepIn_mono (fun y hy => ?_) (key x' i))
    exact hy.symm

/-- The refined coarse path: for an L-path `l` of coarse sites from `a` to `b`, the sites `2h a` and
`2h b` are joined by an L-path of sites each within `ℓ^∞`-distance `h` of some `2h x`, `x ∈ l`
(HA5 D9, step (2): "the straight fine segments `x_j → x_{j+1}`"). -/
theorem reflTransGen_scaleSite_of_isChain (h : ℕ) {l : List (Zd d)} (hl : l.IsChain LAdj)
    {a b : Zd d} (ha : l.head? = some a) (hb : l.getLast? = some b) :
    ReflTransGen (StepIn {y | ∃ x ∈ l, WithinInf (h : ℤ) y (scaleSite (2 * h) x)} LAdj)
      (scaleSite (2 * h) a) (scaleSite (2 * h) b) := by
  set Γ : Set (Zd d) := {y | ∃ x ∈ l, WithinInf (h : ℤ) y (scaleSite (2 * h) x)} with hΓ
  have hl' : l.IsChain fun x y => LAdj x y ∧ x ∈ l ∧ y ∈ l :=
    Perc.isChain_and_of_forall hl fun z hz => hz
  refine List.IsChain.induction
    (fun z => ReflTransGen (StepIn Γ LAdj) (scaleSite (2 * h) a) (scaleSite (2 * h) z)) l hl'
    (fun x y hxy hx => hx.trans (Perc.reflTransGen_stepIn_mono (fun w hw => ?_)
      (reflTransGen_scaleSite_of_lAdj h hxy.1))) (fun lne => ?_) b (List.mem_of_getLast? hb)
  · rcases hw with hw | hw
    · exact ⟨x, hxy.2.1, hw⟩
    · exact ⟨y, hxy.2.2, hw⟩
  · obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.1 ha
    exact ReflTransGen.refl

/-! ### Steps (2)–(3): the open fine path -/

/-- **Steps (2)–(3) of HA5 D9** (DGZ Lemma 3.3, Step 3, with the surgery lemma in place of the
duality argument; HA5 finding G1). Let `B, u ≥ 1` (in the application `B = 2^m`, `u = 2^{k-4}`), and
let `x₁ = 0, …, x_J = B e₁` be an L-path of coarse sites with `|x_j|_∞ ≤ 2B - 1`. Let `O` be a set
of (open) fine sites such that every closed cluster meeting `B̄_{32uB}(0)` has `ℓ^∞`-diameter
`≤ 4u`, and the fine sites `0` and `16uB e₁` are open and not enclosed. Then there are distinct open
fine sites `y₁ = 0, …, y_K = 16uB e₁`, consecutive ones L-adjacent, each within `ℓ^∞`-distance
`14 u` of `16u x` for some `x` of the coarse path. -/
theorem exists_finePath {B u : ℕ} (hu : 1 ≤ u) {xs : List (Zd d)} (hxch : xs.IsChain LAdj)
    (hxh : xs.head? = some 0) (hxl : xs.getLast? = some (latE1 d B))
    (hxB : ∀ x ∈ xs, ∀ i, |x i| ≤ 2 * (B : ℤ) - 1) (O : Set (Zd d))
    (hdiam : ∀ C, IsClosedCluster O C → (∃ z ∈ C, WithinInf ((32 * u * B : ℕ) : ℤ) z 0) →
      ∀ y ∈ C, ∀ y' ∈ C, WithinInf ((4 * u : ℕ) : ℤ) y y')
    (h0 : (0 : Zd d) ∈ O) (h1 : latE1 d (16 * u * B) ∈ O)
    (hencl0 : ∀ C, IsClosedCluster O C → ¬ Encloses C 0)
    (hencl1 : ∀ C, IsClosedCluster O C → ¬ Encloses C (latE1 d (16 * u * B))) :
    ∃ ys : List (Zd d), ys.Nodup ∧ ys.IsChain LAdj ∧ ys.head? = some 0 ∧
      ys.getLast? = some (latE1 d (16 * u * B)) ∧
      ∀ y ∈ ys, y ∈ O ∧ ∃ x ∈ xs, WithinInf (14 * (u : ℤ)) y (scaleSite (16 * u) x) := by
  classical
  set e : Zd d := latE1 d (16 * u * B) with he
  set Γ : Set (Zd d) :=
    {y | ∃ x ∈ xs, WithinInf ((8 * u : ℕ) : ℤ) y (scaleSite (2 * (8 * u : ℕ)) x)} with hΓ
  -- the fine reference path
  have hΓpath : ReflTransGen (StepIn Γ LAdj) 0 e := by
    have h := reflTransGen_scaleSite_of_isChain (8 * u) hxch hxh hxl
    rw [scaleSite_zero, scaleSite_latE1] at h
    have e' : ((2 * (8 * u : ℕ) : ℤ) * (B : ℤ)) = ((16 * u * B : ℕ) : ℤ) := by push_cast; ring
    rw [e'] at h
    exact h
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hΓpath
  set γ : List (Zd d) := 0 :: l with hγ
  have h0xs : (0 : Zd d) ∈ xs := List.mem_of_mem_head? hxh
  have h0Γ : (0 : Zd d) ∈ Γ :=
    ⟨0, h0xs, by rw [scaleSite_zero]; exact Perc.withinInf_refl (by positivity) 0⟩
  have hγch : γ.IsChain LAdj := hl.imp fun _ _ h => h.2.2
  have hγΓ : ∀ y ∈ γ, y ∈ Γ :=
    List.IsChain.induction (fun y => y ∈ Γ) γ hl (fun _ _ hxy _ => hxy.2.1) (fun _ => h0Γ)
  have hγh : γ.head? = some 0 := rfl
  have hγl : γ.getLast? = some e := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil 0 l), hlast]
  -- every site of the reference path is in `B̄_{32uB - 8u}(0)`
  have hΓbound : ∀ y ∈ Γ, ∀ i, |y i| ≤ 32 * (u : ℤ) * B - 8 * u := by
    rintro y ⟨x, hx, hyx⟩ i
    have h1 := hyx i
    have h2 := hxB x hx i
    rw [scaleSite_apply] at h1
    push_cast at h1
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith
  -- the surgery lemma
  set R : ℤ := ((32 * u * B : ℕ) : ℤ) with hR
  have hsurg := Perc.surgeryLemma d O (4 * u) R γ 0 e hγch hγh hγl h0 h1 (by
    intro C hC hCγ
    obtain ⟨z, hzγ, hzC⟩ := hCγ
    have hzB := hΓbound z (hγΓ z hzγ)
    have hzN : WithinInf R z 0 := fun i => by
      rw [Pi.zero_apply, sub_zero, hR]; push_cast; linarith [hzB i]
    have hdC := hdiam C hC ⟨z, hzC, hzN⟩
    have hbox : ∀ c ∈ C, WithinInf R c 0 := by
      intro c hc i
      have h1 := hdC c hc z hzC i
      have h2 := hzB i
      rw [Pi.zero_apply, sub_zero, hR]
      push_cast at h1 ⊢
      rw [abs_le] at h1 h2 ⊢
      constructor <;> nlinarith
    refine ⟨hdC, hbox, ?_, ?_⟩
    · by_contra hext
      exact hencl0 C hC ⟨R, hbox, fun h0C => hC.2.1 h0C h0, hext⟩
    · by_contra hext
      exact hencl1 C hC ⟨R, hbox, fun h1C => hC.2.1 h1C h1, hext⟩)
  -- loop erasure
  have h0S : (0 : Zd d) ∈ {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf (((4 * u : ℕ) : ℤ) + 1) y x} :=
    ⟨h0, 0, List.mem_cons_self, Perc.withinInf_refl (by positivity) 0⟩
  obtain ⟨ys, hynd, hych, hyh, hyl, hyS⟩ := exists_nodup_isChain_of_reflTransGen h0S hsurg
  refine ⟨ys, hynd, hych, hyh, hyl, fun y hy => ⟨(hyS y hy).1, ?_⟩⟩
  obtain ⟨z, hzγ, hyz⟩ := (hyS y hy).2
  obtain ⟨x, hx, hzx⟩ := hγΓ z hzγ
  have hsc : (2 * ((8 * u : ℕ) : ℤ)) = 16 * (u : ℤ) := by push_cast; ring
  rw [hsc] at hzx
  refine ⟨x, hx, (hyz.trans hzx).mono ?_⟩
  push_cast
  have : (1 : ℤ) ≤ u := by exact_mod_cast hu
  linarith

/-! ### Step (4): the chain bound -/

/-- Every entry `l.getD i 0` of a list starting with `0` lies in the list. -/
theorem getD_mem_of_head {l : List (Zd d)} (h : l.head? = some 0) (i : ℕ) : l.getD i 0 ∈ l := by
  by_cases hi : i < l.length
  · exact Perc.getD_mem hi
  · rw [List.getD_eq_default l 0 (not_lt.1 hi)]
    exact List.mem_of_mem_head? h

open Classical in
/-- **Counting** (HA5 D9, step (4): at most `(2r+1)^d` of the distinct fine sites `y_i` carry a
given coarse label `x`, as they lie in `B̄_r(L x)`). If the entries `y_i` (`i < K`) of a
duplicate-free list are labelled by sites `lab y_i ∈ xs` with `|y_i - L lab y_i|_∞ ≤ r`, then for
`g ≥ 0`,
`∑_{i<K} g(lab y_i) ≤ (2r+1)^d ∑_{x ∈ xs} g x`. -/
theorem sum_comp_le {ys xs : List (Zd d)} (hynd : ys.Nodup) {r : ℕ} {L : ℤ}
    (lab : Zd d → Zd d)
    (hlab : ∀ y ∈ ys, lab y ∈ xs ∧ WithinInf (r : ℤ) y (scaleSite L (lab y)))
    {g : Zd d → ℝ} (hg : ∀ x, 0 ≤ g x) {K : ℕ} (hK : K ≤ ys.length) :
    ∑ i ∈ Finset.range K, g (lab (ys.getD i 0)) ≤
      (((2 * r + 1) ^ d : ℕ) : ℝ) * ∑ x ∈ xs.toFinset, g x := by
  rw [Finset.sum_comp g (fun i => lab (ys.getD i 0))]
  have hfib : ∀ x, ((Finset.range K).filter fun i => lab (ys.getD i 0) = x).card ≤
      (2 * r + 1) ^ d := by
    intro x
    rw [← Perc.card_boxF (scaleSite L x) r]
    refine Finset.card_le_card_of_injOn (fun i => ys.getD i 0) ?_ ?_
    · intro i hi
      rw [Finset.coe_filter, mem_ofPred_eq, Finset.mem_range] at hi
      rw [Finset.mem_coe, Perc.mem_boxF]
      have h := (hlab _ (Perc.getD_mem (lt_of_lt_of_le hi.1 hK))).2
      rw [hi.2] at h
      exact h
    · intro i hi j hj hij
      rw [Finset.coe_filter, mem_ofPred_eq, Finset.mem_range] at hi hj
      have hi' := lt_of_lt_of_le hi.1 hK
      have hj' := lt_of_lt_of_le hj.1 hK
      simp only at hij
      rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
      exact hynd.getElem_inj_iff.1 hij
  calc ∑ x ∈ (Finset.range K).image (fun i => lab (ys.getD i 0)),
        ((Finset.range K).filter fun i => lab (ys.getD i 0) = x).card • g x
      ≤ ∑ x ∈ (Finset.range K).image (fun i => lab (ys.getD i 0)),
          (((2 * r + 1) ^ d : ℕ) : ℝ) * g x := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib x) (hg x)
    _ ≤ ∑ x ∈ xs.toFinset, (((2 * r + 1) ^ d : ℕ) : ℝ) * g x := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ =>
          mul_nonneg (by positivity) (hg x)
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        rw [List.mem_toFinset]
        exact (hlab _ (Perc.getD_mem (lt_of_lt_of_le (Finset.mem_range.1 hi) hK))).1
    _ = (((2 * r + 1) ^ d : ℕ) : ℝ) * ∑ x ∈ xs.toFinset, g x := by rw [Finset.mul_sum]

/-- Location of a fine site near a scaled coarse site: if `|x|_∞ ≤ 2B - 1` and
`|y - 16u x|_∞ ≤ 14u`, then `|s' y|_∞ ≤ 2 - 2u s'` for `s = 16u s'`, `sB = 1` (HA5 D9: the fine
sites used satisfy `|y|_∞ ≤ 2 - 2^{-m-3}`). -/
theorem abs_latPt_fine_le {B u : ℕ} {s s' : ℝ} (hs' : 0 < s') (hss' : s = 16 * u * s')
    (hsB : s * B = 1) {x y : Zd d} (hxB : ∀ i, |x i| ≤ 2 * (B : ℤ) - 1)
    (hyx : WithinInf (14 * (u : ℤ)) y (scaleSite (16 * u) x)) (i : Fin d) :
    |latPt s' y i| ≤ 2 - 2 * u * s' := by
  have hint : |y i| ≤ 32 * (u : ℤ) * B - 2 * u := by
    have h1 := hyx i
    have h2 := hxB i
    rw [scaleSite_apply] at h1
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith
  have hreal : |(y i : ℝ)| ≤ 32 * (u : ℝ) * B - 2 * u := by exact_mod_cast hint
  rw [latPt_apply, abs_mul, abs_of_pos hs']
  have e : s' * (32 * (u : ℝ) * B - 2 * u) = 2 - 2 * u * s' := by
    have : 16 * (u : ℝ) * s' * B = 1 := by rw [← hss']; exact hsB
    linear_combination 2 * this
  rw [← e]
  exact mul_le_mul_of_nonneg_left hreal hs'.le

/-- The fine site `y` is within `ℓ^∞`-distance `14 u s'` of the coarse point `s x` when
`|y - 16u x|_∞ ≤ 14u` and `s = 16u s'`. -/
theorem abs_latPt_fine_sub_le {u : ℕ} {s s' : ℝ} (hs' : 0 < s') (hss' : s = 16 * u * s')
    {x y : Zd d} (hyx : WithinInf (14 * (u : ℤ)) y (scaleSite (16 * u) x)) (i : Fin d) :
    |latPt s' y i - latPt s x i| ≤ 14 * u * s' := by
  have h1 := hyx i
  rw [scaleSite_apply] at h1
  have h1' : |((y i - 16 * u * x i : ℤ) : ℝ)| ≤ 14 * u := by exact_mod_cast h1
  rw [latPt_apply, latPt_apply, hss']
  have e : s' * (y i : ℝ) - 16 * u * s' * x i = s' * ((y i - 16 * u * x i : ℤ) : ℝ) := by
    push_cast; ring
  rw [e, abs_mul, abs_of_pos hs']
  calc s' * |((y i - 16 * u * x i : ℤ) : ℝ)| ≤ s' * (14 * u) :=
        mul_le_mul_of_nonneg_left h1' hs'.le
    _ = 14 * u * s' := by ring

/-- **Step (4) of HA5 D9** (DGZ Lemma 3.3, Step 4). Let `s = 16u s'`, `sB = 1` (`u ≥ 1`), and let
`y₁ = 0, …, y_K = 16uB e₁` be distinct fine sites, consecutive ones L-adjacent, each within
`14 u` of `16u x` for a coarse site `x ∈ xs` with `|x|_∞ ≤ 2B - 1`. Assume: `|φ₀ - φ₀(s x)| ≤ θ`
on `cbox (s x) (3 s)` (`x ∈ xs`), `φ₁ ≤ S` on `U`, and every `y_i` is open: the internal distance
of `φ₂` in `obox (s' y_i) (2 s')` from `s' y_i` to each L-neighbour is `≤ s' b`. Then for `ξ ≥ 0`,
`D^ξ(φ₀ + φ₁ + φ₂) ≤ e^{ξ(θ + S)} b (32u + 1)^d s' ∑_{x ∈ xs} e^{ξ φ₀(s x)}`. -/
theorem lfppDistance_le_of_finePath (hd : 0 < d) {B u : ℕ} (hu : 1 ≤ u) {s s' : ℝ}
    (hs' : 0 < s') (hss' : s = 16 * u * s') (hsB : s * B = 1) {ξ θ S b : ℝ} (hξ : 0 ≤ ξ)
    {φ₀ φ₁ φ₂ : Rd d → ℝ} (h₀ : Continuous φ₀) (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    {xs ys : List (Zd d)} (hxB : ∀ x ∈ xs, ∀ i, |x i| ≤ 2 * (B : ℤ) - 1)
    (hosc : ∀ x ∈ xs, ∀ z ∈ cbox (latPt s x) (3 * s), |φ₀ z - φ₀ (latPt s x)| ≤ θ)
    (hsup : ∀ z ∈ cube d, φ₁ z ≤ S)
    (hynd : ys.Nodup) (hych : ys.IsChain LAdj) (hyh : ys.head? = some 0)
    (hyl : ys.getLast? = some (latE1 d (16 * u * B)))
    (hyO : ∀ y ∈ ys, ∀ y', LAdj y y' →
      lfppDistOn ξ φ₂ (obox (latPt s' y) (2 * s')) (latPt s' y) (latPt s' y') ≤ s' * b)
    (hynear : ∀ y ∈ ys, ∃ x ∈ xs, WithinInf (14 * (u : ℤ)) y (scaleSite (16 * u) x)) :
    lfppDistance d ξ (fun z => φ₀ z + φ₁ z + φ₂ z) ≤
      Real.exp (ξ * (θ + S)) * b * (((2 * (16 * u) + 1) ^ d : ℕ) : ℝ) * s' *
        ∑ x ∈ xs.toFinset, Real.exp (ξ * φ₀ (latPt s x)) := by
  classical
  have hφ : Continuous fun z => φ₀ z + φ₁ z + φ₂ z := (h₀.add h₁).add h₂
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hs : 0 < s := by rw [hss']; positivity
  choose! lab hlab using hynear
  have hmem : ∀ i, ys.getD i 0 ∈ ys := getD_mem_of_head hyh
  set K := ys.length - 1 with hKdef
  set v : ℕ → Rd d := fun i => latPt s' (ys.getD i 0) with hv
  -- `b ≥ 0`: the site `0` is open
  have hb : 0 ≤ b := by
    have h := hyO 0 (List.mem_of_mem_head? hyh) _ (Perc.lAdj_add_single 0 ⟨0, hd⟩)
    exact (mul_nonneg_iff_of_pos_left hs').1
      ((lfppDistOn_nonneg _ _ _ _ _).trans h)
  -- the boxes lie in `U` and in the coarse boxes
  have hboxU : ∀ y ∈ ys, obox (latPt s' y) (2 * s') ⊆ cube d := by
    intro y hy w hw i
    have h1 := abs_latPt_fine_le hs' hss' hsB (hxB _ (hlab y hy).1) (hlab y hy).2 i
    have h2 := hw i
    have h3 := abs_sub_abs_le_abs_sub (w i) (latPt s' y i)
    nlinarith
  have hboxC : ∀ y ∈ ys, obox (latPt s' y) (2 * s') ⊆ cbox (latPt s (lab y)) (3 * s) := by
    intro y hy w hw i
    have h1 := abs_latPt_fine_sub_le hs' hss' (hlab y hy).2 i
    have h2 := hw i
    have h3 := abs_sub_le (w i) (latPt s' y i) (latPt s (lab y) i)
    have h4 : 2 * s' + 14 * u * s' ≤ 3 * s := by rw [hss']; nlinarith
    linarith
  -- the chain bound
  have h0 : v 0 = 0 := by
    simp only [hv, Perc.getD_zero_of_head? hyh, latPt_zero]
  have hK : v K = e₁ d := by
    simp only [hv, hKdef, Perc.getD_last_of_getLast? hyl]
    refine latPt_latE1 ?_
    push_cast
    rw [← hsB, hss']; ring
  have hlen : 2 ≤ ys.length := by
    by_contra hcon
    have hyl' := hyl
    have h1 : ys.length = 1 := by
      have : ys ≠ [] := by rintro rfl; simp at hyh
      have := List.length_pos_of_ne_nil this
      omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h1
    simp only [List.head?_cons, Option.some.injEq] at hyh
    simp only [List.getLast?_singleton, Option.some.injEq] at hyl'
    have hne := e₁_ne_zero hd
    rw [← latPt_latE1 (s := s') (N := 16 * u * B) (by push_cast; rw [← hsB, hss']; ring),
      ← hyl', hyh, latPt_zero] at hne
    exact hne rfl
  have hadj : ∀ i < K, LAdj (ys.getD i 0) (ys.getD (i + 1) 0) := fun i hi =>
    Perc.getD_chain hych (by omega)
  have hjoin : ∀ i < K, PcwJoined (obox (v i) (2 * s')) (v i) (v (i + 1)) := by
    intro i hi
    refine PcwJoined.of_convex (convex_obox _ _) (mem_obox_self _ (by positivity)) fun l => ?_
    have h := (hadj i hi).withinInf l
    have h' : |((ys.getD (i + 1) 0 l : ℤ) : ℝ) - ((ys.getD i 0 l : ℤ) : ℝ)| ≤ 1 := by
      rw [abs_sub_comm]; exact_mod_cast h
    simp only [hv, latPt_apply]
    rw [← mul_sub, abs_mul, abs_of_pos hs']
    nlinarith
  have hchain := lfppDistOn_le_sum (ζ := ξ) hφ v (fun i => obox (v i) (2 * s'))
    (fun i => hboxU _ (hmem i)) K hjoin
  rw [h0, hK, ← lfppDistance_eq_lfppDistOn] at hchain
  -- each step
  have hstep : ∀ i < K, lfppDistOn ξ (fun z => φ₀ z + φ₁ z + φ₂ z) (obox (v i) (2 * s')) (v i)
      (v (i + 1)) ≤ Real.exp (ξ * (θ + S)) * (s' * b) *
        Real.exp (ξ * φ₀ (latPt s (lab (ys.getD i 0)))) := by
    intro i hi
    set y := ys.getD i 0 with hy
    set c := latPt s (lab y) with hc
    have hle := lfppDistOn_le_mul_of_exp_le (ζ := ξ) (V := obox (v i) (2 * s'))
      (x := v i) (y := v (i + 1)) hφ h₂ (C := Real.exp (ξ * (θ + S)) * Real.exp (ξ * φ₀ c))
      (by positivity) (fun z hz => ?_)
    · refine hle.trans ?_
      have h2 := hyO y (hmem i) _ (hadj i hi)
      calc Real.exp (ξ * (θ + S)) * Real.exp (ξ * φ₀ c) *
            lfppDistOn ξ φ₂ (obox (v i) (2 * s')) (v i) (v (i + 1))
          ≤ Real.exp (ξ * (θ + S)) * Real.exp (ξ * φ₀ c) * (s' * b) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.exp (ξ * (θ + S)) * (s' * b) * Real.exp (ξ * φ₀ c) := by ring
    · have hzU := hboxU y (hmem i) hz
      have hzC := hboxC y (hmem i) hz
      have h1 := hosc _ (hlab y (hmem i)).1 z hzC
      have h3 := hsup z hzU
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h4 : φ₀ z ≤ φ₀ c + θ := by linarith [le_abs_self (φ₀ z - φ₀ c)]
      have h5 : ξ * φ₀ z ≤ ξ * (φ₀ c + θ) := mul_le_mul_of_nonneg_left h4 hξ
      have h6 : ξ * φ₁ z ≤ ξ * S := mul_le_mul_of_nonneg_left h3 hξ
      nlinarith
  -- the sum and the count
  have hcount := sum_comp_le (r := 16 * u) (L := 16 * u) hynd lab
    (fun y hy => ⟨(hlab y hy).1, (hlab y hy).2.mono (by push_cast; linarith)⟩)
    (g := fun x => Real.exp (ξ * φ₀ (latPt s x))) (fun x => (Real.exp_pos _).le)
    (K := K) (by omega)
  calc lfppDistance d ξ (fun z => φ₀ z + φ₁ z + φ₂ z)
      ≤ ∑ i ∈ Finset.range K, lfppDistOn ξ (fun z => φ₀ z + φ₁ z + φ₂ z)
          (obox (v i) (2 * s')) (v i) (v (i + 1)) := hchain
    _ ≤ ∑ i ∈ Finset.range K, Real.exp (ξ * (θ + S)) * (s' * b) *
          Real.exp (ξ * φ₀ (latPt s (lab (ys.getD i 0)))) :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.1 hi)
    _ = Real.exp (ξ * (θ + S)) * (s' * b) *
          ∑ i ∈ Finset.range K, Real.exp (ξ * φ₀ (latPt s (lab (ys.getD i 0)))) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (ξ * (θ + S)) * (s' * b) * ((((2 * (16 * u) + 1) ^ d : ℕ) : ℝ) *
          ∑ x ∈ xs.toFinset, Real.exp (ξ * φ₀ (latPt s x))) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = Real.exp (ξ * (θ + S)) * b * (((2 * (16 * u) + 1) ^ d : ℕ) : ℝ) * s' *
          ∑ x ∈ xs.toFinset, Real.exp (ξ * φ₀ (latPt s x)) := by ring

/-! ### Target T2 -/

/-- **Target T2** (HA5 D9, "Construction on E", steps (1)–(4); DGZ Lemma 3.3, Steps 2–4, with the
surgery lemma in place of the duality argument). Let `d ≥ 1`, `m ≥ 3`, `k ≥ 4`, `ξ ≥ 0`,
`s = 2^{-m}`, `s' = 2^{-m-k}`, and let `φ₀, φ₁, φ₂` be continuous fields. Assume the good event:
* (`E₁`) `|φ₀ - φ₀(s x)| ≤ θ` on `cbox (s x) (3 s)` for every coarse site `x` with `s x ∈ U`, and
  `φ₁ ≤ S` on `U`;
* (`E₂`) an admissible path `P` with `∫_P e^{ξ φ₀} |dz| ≤ 2a`;
* (open sites) every fine site `y ∈ O` with `|s' y|_∞ ≤ 2 - 2^{-m-3}` satisfies
  `D^ξ_{obox (s' y) (2 s')}(s' y, s' y')(φ₂) ≤ s' b` for each L-neighbour `y'`;
* (`E₃ₐ`) every closed cluster (maximal `*`-connected set of sites outside `O`) meeting
  `B̄_{2^{m+k+1}}(0)` has `ℓ^∞`-diameter `≤ 2^{k-2}`;
* (`E₃ᵦ`) the fine sites `0` and `2^{m+k} e₁` are in `O` and not enclosed by a closed cluster.
Then `D^ξ(φ₀ + φ₁ + φ₂) ≤ (8/7) 7^d ((2^{k+1}+1)^d / 2^k) e^{2ξθ + ξS} a b`. -/
theorem lfppDistance_le_of_good (hd : 0 < d) {m k : ℕ} (hm : 3 ≤ m) (hk : 4 ≤ k)
    {ξ θ S a b : ℝ} (hξ : 0 ≤ ξ) {φ₀ φ₁ φ₂ : Rd d → ℝ} (h₀ : Continuous φ₀)
    (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hosc : ∀ x : Zd d, latPt ((2 : ℝ)⁻¹ ^ m) x ∈ cube d →
      ∀ z ∈ cbox (latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * (2 : ℝ)⁻¹ ^ m),
        |φ₀ z - φ₀ (latPt ((2 : ℝ)⁻¹ ^ m) x)| ≤ θ)
    (hsup : ∀ z ∈ cube d, φ₁ z ≤ S)
    {P : ℝ → Rd d} (hP : IsAdmissiblePath d P) (hPa : lfppLength ξ φ₀ P ≤ 2 * a)
    (O : Set (Zd d))
    (hO : ∀ y ∈ O, (∀ i, |latPt ((2 : ℝ)⁻¹ ^ (m + k)) y i| ≤ 2 - (2 : ℝ)⁻¹ ^ (m + 3)) →
      ∀ y', LAdj y y' →
        lfppDistOn ξ φ₂ (obox (latPt ((2 : ℝ)⁻¹ ^ (m + k)) y) (2 * (2 : ℝ)⁻¹ ^ (m + k)))
          (latPt ((2 : ℝ)⁻¹ ^ (m + k)) y) (latPt ((2 : ℝ)⁻¹ ^ (m + k)) y') ≤
          (2 : ℝ)⁻¹ ^ (m + k) * b)
    (hdiam : ∀ C, IsClosedCluster O C → (∃ z ∈ C, WithinInf ((2 ^ (m + k + 1) : ℕ) : ℤ) z 0) →
      ∀ y ∈ C, ∀ y' ∈ C, WithinInf ((2 ^ (k - 2) : ℕ) : ℤ) y y')
    (h0 : (0 : Zd d) ∈ O) (h1 : latE1 d (2 ^ (m + k)) ∈ O)
    (hencl0 : ∀ C, IsClosedCluster O C → ¬ Encloses C 0)
    (hencl1 : ∀ C, IsClosedCluster O C → ¬ Encloses C (latE1 d (2 ^ (m + k)))) :
    lfppDistance d ξ (fun z => φ₀ z + φ₁ z + φ₂ z) ≤
      8 / 7 * 7 ^ d * (((2 : ℝ) ^ (k + 1) + 1) ^ d / 2 ^ k) *
        Real.exp (2 * ξ * θ + ξ * S) * a * b := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  set s : ℝ := (2 : ℝ)⁻¹ ^ m with hs_def
  set s' : ℝ := (2 : ℝ)⁻¹ ^ (m + (j + 4)) with hs'_def
  set B : ℕ := 2 ^ m with hB
  set u : ℕ := 2 ^ j with hu_def
  have hu : 1 ≤ u := Nat.one_le_two_pow
  have hs' : 0 < s' := by positivity
  have hs : 0 < s := by positivity
  have hss' : s = 16 * u * s' := by
    simp only [hs_def, hs'_def, hu_def, pow_add]
    push_cast
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
    have h2 : (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
    have h4 : (2 : ℝ) ^ 4 * (2 : ℝ)⁻¹ ^ 4 = 1 := by norm_num
    calc (2 : ℝ)⁻¹ ^ m = (2 : ℝ)⁻¹ ^ m * ((2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j) *
          ((2 : ℝ) ^ 4 * (2 : ℝ)⁻¹ ^ 4) := by rw [h2, h4]; ring
      _ = 2 ^ 4 * 2 ^ j * ((2 : ℝ)⁻¹ ^ m * ((2 : ℝ)⁻¹ ^ j * (2 : ℝ)⁻¹ ^ 4)) := by ring
  have hsB : s * B = 1 := by
    simp only [hs_def, hB]; push_cast
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have hab : 0 ≤ a := by linarith [lfppLength_nonneg ξ φ₀ P]
  -- step (1): the coarse path and (3.20′)
  obtain ⟨xs, -, hxch, hxh, hxl, hxS, hsum⟩ := exists_coarsePath (ξ := ξ) hd hm h₀ hP hosc
  have hxB : ∀ x ∈ xs, ∀ i, |x i| ≤ 2 * (B : ℤ) - 1 := by
    intro x hx i
    have h := (hxS x hx).1 i
    rw [latPt_apply, abs_mul, abs_of_pos hs] at h
    have h' : |(x i : ℝ)| < 2 * B := by
      have hBpos : (0 : ℝ) < B := by positivity
      have : s * |(x i : ℝ)| < 2 * (s * B) := by rw [hsB]; linarith
      nlinarith
    have h'' : |x i| < 2 * (B : ℤ) := by exact_mod_cast h'
    omega
  -- steps (2)–(3): the open fine path
  have eN : (16 * (u : ℤ) * (B : ℤ)) = 2 ^ (m + (j + 4)) := by
    simp only [hu_def, hB]; push_cast; ring
  have hxl' : xs.getLast? = some (latE1 d (B : ℤ)) := by
    rw [hxl]; simp only [hB]; push_cast; rfl
  obtain ⟨ys, hynd, hych, hyh, hyl, hyO⟩ := exists_finePath hu hxch hxh hxl' hxB O
    (fun C hC hCz y hy y' hy' => by
      have e1 : ((32 * u * B : ℕ) : ℤ) = ((2 ^ (m + (j + 4) + 1) : ℕ) : ℤ) := by
        simp only [hu_def, hB]; push_cast; ring
      have e2 : ((4 * u : ℕ) : ℤ) = ((2 ^ (j + 4 - 2) : ℕ) : ℤ) := by
        rw [show j + 4 - 2 = j + 2 by omega]
        simp only [hu_def]; push_cast; ring
      rw [e1] at hCz
      rw [e2]
      exact hdiam C hC hCz y hy y' hy')
    h0 (by rw [eN]; exact h1) hencl0 (by rw [eN]; exact hencl1)
  rw [eN] at hyl
  -- step (4): the chain bound
  have hyO' : ∀ y ∈ ys, ∀ y', LAdj y y' →
      lfppDistOn ξ φ₂ (obox (latPt s' y) (2 * s')) (latPt s' y) (latPt s' y') ≤ s' * b := by
    intro y hy y' hyy'
    obtain ⟨hyOm, x, hx, hyx⟩ := hyO y hy
    refine hO y hyOm (fun i => ?_) y' hyy'
    have h := abs_latPt_fine_le hs' hss' hsB (hxB x hx) hyx i
    have e : 2 * (u : ℝ) * s' = (2 : ℝ)⁻¹ ^ (m + 3) := by
      simp only [hu_def, hs'_def]; push_cast
      rw [pow_add, pow_add, pow_add]
      have h2 : (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
      calc 2 * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m * ((2 : ℝ)⁻¹ ^ j * (2 : ℝ)⁻¹ ^ 4))
          = (2 : ℝ)⁻¹ ^ m * ((2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j) * (2 * (2 : ℝ)⁻¹ ^ 4) := by ring
        _ = (2 : ℝ)⁻¹ ^ m * (2 : ℝ)⁻¹ ^ 3 := by rw [h2]; norm_num
    rw [← e]
    exact h
  have hchain := lfppDistance_le_of_finePath (ξ := ξ) (θ := θ) (S := S) (b := b) hd hu hs' hss'
    hsB hξ h₀ h₁ h₂ hxB (fun x hx => hosc x (hxS x hx).1) hsup hynd hych hyh
    (by rw [← eN] at hyl; exact hyl) hyO' (fun y hy => (hyO y hy).2)
  -- `b ≥ 0`
  have hb : 0 ≤ b := by
    have h := hyO' 0 (List.mem_of_mem_head? hyh) _ (Perc.lAdj_add_single 0 ⟨0, hd⟩)
    exact (mul_nonneg_iff_of_pos_left hs').1 ((lfppDistOn_nonneg _ _ _ _ _).trans h)
  -- (3.20′)
  set G : ℝ := ∑ x ∈ xs.toFinset, Real.exp (ξ * φ₀ (latPt s x)) with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun x _ => (Real.exp_pos _).le
  have hsG : s * G ≤ 4 / 7 * 7 ^ d * Real.exp (ξ * θ) * (2 * a) := by
    rw [hG, Finset.mul_sum]
    refine hsum.trans ?_
    rw [abs_of_nonneg hξ]
    exact mul_le_mul_of_nonneg_left hPa (by positivity)
  -- assembling the constants
  have hNcast : (((2 * (16 * u) + 1) ^ d : ℕ) : ℝ) = ((2 : ℝ) ^ (j + 4 + 1) + 1) ^ d := by
    simp only [hu_def]; push_cast; ring
  have h16 : (2 : ℝ) ^ (j + 4) = 16 * u := by simp only [hu_def]; push_cast; ring
  rw [hNcast] at hchain
  set N : ℝ := ((2 : ℝ) ^ (j + 4 + 1) + 1) ^ d with hN
  have hN0 : 0 ≤ N := by positivity
  have hu0 : (0 : ℝ) < 16 * u := by positivity
  calc lfppDistance d ξ (fun z => φ₀ z + φ₁ z + φ₂ z)
      ≤ Real.exp (ξ * (θ + S)) * b * N * s' * G := hchain
    _ = Real.exp (ξ * (θ + S)) * b * N / (16 * u) * (s * G) := by
        rw [hss']; field_simp
    _ ≤ Real.exp (ξ * (θ + S)) * b * N / (16 * u) *
          (4 / 7 * 7 ^ d * Real.exp (ξ * θ) * (2 * a)) :=
        mul_le_mul_of_nonneg_left hsG (by positivity)
    _ = 8 / 7 * 7 ^ d * (N / 2 ^ (j + 4)) *
          (Real.exp (ξ * (θ + S)) * Real.exp (ξ * θ)) * a * b := by
        rw [h16]; ring
    _ = 8 / 7 * 7 ^ d * (N / 2 ^ (j + 4)) * Real.exp (2 * ξ * θ + ξ * S) * a * b := by
        rw [← Real.exp_add]; ring_nf

/-! ### Target T2 with DGZ's parameters -/

/-- `log n ≤ 3 n^{1/3}` for `n > 0`. -/
theorem log_le_three_mul_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 3 * x ^ (1 / 3 : ℝ) := by
  have h1 : Real.log (x ^ (1 / 3 : ℝ)) = 1 / 3 * Real.log x := Real.log_rpow hx _
  have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / 3 : ℝ))
  linarith

/-- `(log m)² ≤ 9 n^{2/3}` for `1 ≤ m ≤ n`. -/
theorem log_sq_le_nine_mul_rpow {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.log m ^ 2 ≤ 9 * n ^ (2 / 3 : ℝ) := by
  have hn : 0 < n := by linarith
  have h0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have h1 : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn
  have h2 := log_le_three_mul_rpow hn
  have h3 : (n ^ (1 / 3 : ℝ)) ^ 2 = n ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  calc Real.log m ^ 2 ≤ (3 * n ^ (1 / 3 : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ h0 (h1.trans h2) 2
    _ = 9 * n ^ (2 / 3 : ℝ) := by rw [mul_pow, h3]; norm_num

/-- The combinatorial constant of `lfppDistance_le_of_good` is `e^{O(k d)}`:
`(8/7) 7^d (2^{k+1}+1)^d / 2^k ≤ e^{1 + (k + 5) d}`. -/
theorem const_le_exp (d k : ℕ) :
    8 / 7 * 7 ^ d * (((2 : ℝ) ^ (k + 1) + 1) ^ d / 2 ^ k) ≤
      Real.exp (1 + ((k : ℝ) + 5) * d) := by
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hA : ((2 : ℝ) ^ (k + 1) + 1) ^ d / 2 ^ k ≤ (3 * 2 ^ k) ^ d := by
    refine (div_le_self (by positivity) h2k).trans (pow_le_pow_left₀ (by positivity) ?_ d)
    rw [pow_succ]; linarith
  have hB : (7 : ℝ) ^ d * (3 * 2 ^ k) ^ d ≤ ((2 : ℝ) ^ (k + 5)) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    rw [pow_add]; norm_num; nlinarith
  have hC : ((2 : ℝ) ^ (k + 5)) ^ d ≤ Real.exp (((k : ℝ) + 5) * d) := by
    rw [← pow_mul]
    calc (2 : ℝ) ^ ((k + 5) * d) ≤ Real.exp 1 ^ ((k + 5) * d) :=
          pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp (((k : ℝ) + 5) * d) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
  calc 8 / 7 * 7 ^ d * (((2 : ℝ) ^ (k + 1) + 1) ^ d / 2 ^ k)
      ≤ 8 / 7 * 7 ^ d * (3 * 2 ^ k) ^ d := by gcongr
    _ = 8 / 7 * (7 ^ d * (3 * 2 ^ k) ^ d) := by ring
    _ ≤ 2 * Real.exp (((k : ℝ) + 5) * d) := by
        have := hB.trans hC
        have h0 : (0 : ℝ) ≤ 7 ^ d * (3 * 2 ^ k) ^ d := by positivity
        nlinarith
    _ ≤ Real.exp 1 * Real.exp (((k : ℝ) + 5) * d) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp (1 + ((k : ℝ) + 5) * d) := by rw [Real.exp_add]

/-- **Target T2 with DGZ's parameters** (HA5 D9: `θ = n^{2/3}`, `k = ⌊(log m)²⌋`, `m ≥ m₀ = 8`,
`m ≤ n`): on the good event of `lfppDistance_le_of_good`,
`D^ξ(φ₀ + φ₁ + φ₂) ≤ e^{(14 d + 1 + 2ξ) n^{2/3} + ξ S} a b`. (The constant `C = 14 d + 1 + 2ξ` of
DGZ's `e^{C n^{2/3}}`: the summand `2ξ` comes from the oscillation `n^{2/3}` of `φ₀` entering
through `e^{ξ φ₀}` twice, in (3.20′) and in step (4).) -/
theorem lfppDistance_le_of_good_exp (hd : 0 < d) {n m k : ℕ} (hm : 8 ≤ m) (hmn : m ≤ n)
    (hk : k = ⌊Real.log m ^ 2⌋₊) {ξ S a b : ℝ} (hξ : 0 ≤ ξ) {φ₀ φ₁ φ₂ : Rd d → ℝ}
    (h₀ : Continuous φ₀) (h₁ : Continuous φ₁) (h₂ : Continuous φ₂)
    (hosc : ∀ x : Zd d, latPt ((2 : ℝ)⁻¹ ^ m) x ∈ cube d →
      ∀ z ∈ cbox (latPt ((2 : ℝ)⁻¹ ^ m) x) (3 * (2 : ℝ)⁻¹ ^ m),
        |φ₀ z - φ₀ (latPt ((2 : ℝ)⁻¹ ^ m) x)| ≤ (n : ℝ) ^ (2 / 3 : ℝ))
    (hsup : ∀ z ∈ cube d, φ₁ z ≤ S)
    {P : ℝ → Rd d} (hP : IsAdmissiblePath d P) (hPa : lfppLength ξ φ₀ P ≤ 2 * a)
    (O : Set (Zd d))
    (hO : ∀ y ∈ O, (∀ i, |latPt ((2 : ℝ)⁻¹ ^ (m + k)) y i| ≤ 2 - (2 : ℝ)⁻¹ ^ (m + 3)) →
      ∀ y', LAdj y y' →
        lfppDistOn ξ φ₂ (obox (latPt ((2 : ℝ)⁻¹ ^ (m + k)) y) (2 * (2 : ℝ)⁻¹ ^ (m + k)))
          (latPt ((2 : ℝ)⁻¹ ^ (m + k)) y) (latPt ((2 : ℝ)⁻¹ ^ (m + k)) y') ≤
          (2 : ℝ)⁻¹ ^ (m + k) * b)
    (hdiam : ∀ C, IsClosedCluster O C → (∃ z ∈ C, WithinInf ((2 ^ (m + k + 1) : ℕ) : ℤ) z 0) →
      ∀ y ∈ C, ∀ y' ∈ C, WithinInf ((2 ^ (k - 2) : ℕ) : ℤ) y y')
    (h0 : (0 : Zd d) ∈ O) (h1 : latE1 d (2 ^ (m + k)) ∈ O)
    (hencl0 : ∀ C, IsClosedCluster O C → ¬ Encloses C 0)
    (hencl1 : ∀ C, IsClosedCluster O C → ¬ Encloses C (latE1 d (2 ^ (m + k)))) :
    lfppDistance d ξ (fun z => φ₀ z + φ₁ z + φ₂ z) ≤
      Real.exp ((14 * d + 1 + 2 * ξ) * (n : ℝ) ^ (2 / 3 : ℝ) + ξ * S) * a * b := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  -- `k ≥ 4` and `k ≤ 9 n^{2/3}`
  have hlog8 : 2 < Real.log 8 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have h3 : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have hlogm : 2 < Real.log m :=
    hlog8.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hm))
  have hk4 : 4 ≤ k := by
    rw [hk]
    exact Nat.le_floor (by push_cast; nlinarith)
  have hkle : (k : ℝ) ≤ 9 * (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [hk]
    exact (Nat.floor_le (sq_nonneg _)).trans (log_sq_le_nine_mul_rpow hm1 hmn')
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (hm1.trans hmn') (by norm_num)
  -- the core bound
  have hcore := lfppDistance_le_of_good (θ := (n : ℝ) ^ (2 / 3 : ℝ)) hd (by omega) hk4 hξ h₀ h₁
    h₂ hosc hsup hP hPa O hO hdiam h0 h1 hencl0 hencl1
  -- `a, b ≥ 0`
  have ha : 0 ≤ a := by linarith [lfppLength_nonneg ξ φ₀ P]
  have hb : 0 ≤ b := by
    have hreg : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ (m + k)) (0 : Zd d) i| ≤ 2 - (2 : ℝ)⁻¹ ^ (m + 3) := by
      intro i
      rw [latPt_zero]
      show |(0 : ℝ)| ≤ _
      have : (2 : ℝ)⁻¹ ^ (m + 3) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      rw [abs_zero]; linarith
    have h := hO 0 h0 hreg _ (Perc.lAdj_add_single 0 ⟨0, hd⟩)
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 ((lfppDistOn_nonneg _ _ _ _ _).trans h)
  -- the constant
  have hconst := const_le_exp d k
  have hexp : 1 + ((k : ℝ) + 5) * d ≤ (14 * d + 1) * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  calc lfppDistance d ξ (fun z => φ₀ z + φ₁ z + φ₂ z)
      ≤ 8 / 7 * 7 ^ d * (((2 : ℝ) ^ (k + 1) + 1) ^ d / 2 ^ k) *
          Real.exp (2 * ξ * (n : ℝ) ^ (2 / 3 : ℝ) + ξ * S) * a * b := hcore
    _ ≤ Real.exp ((14 * d + 1) * (n : ℝ) ^ (2 / 3 : ℝ)) *
          Real.exp (2 * ξ * (n : ℝ) ^ (2 / 3 : ℝ) + ξ * S) * a * b := by
        gcongr
        exact hconst.trans (Real.exp_le_exp.2 hexp)
    _ = Real.exp ((14 * d + 1 + 2 * ξ) * (n : ℝ) ^ (2 / 3 : ℝ) + ξ * S) * a * b := by
        rw [← Real.exp_add]; ring_nf

end DGZ

end HigherDimLFPP
