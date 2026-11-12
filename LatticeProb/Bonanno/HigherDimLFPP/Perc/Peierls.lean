/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.Peierls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Lattice
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

/-!
# Peierls bound for finite-range dependent site percolation on `ℤ^d` (HA5 D6(i)–(ii))

Setting (HA5 D6): events `closed x` (`x ∈ ℤ^d`) with `μ (closed x) ≤ ε` and the product bound
`ProductBound μ closed r` (finite-range dependence: for sites pairwise at `ℓ^∞`-distance `> r`,
`μ (⋂ closed) ≤ ∏ μ (closed)`), `θ ≤ 1`, `ε ≤ θ ^ (r+1)^d` and `3^d θ ≤ 1/2`. Then a closed
`*`-path from `x` leaving `B̄_L(x)` has probability at most `2^{-L}` (`peierlsD`).

* `list_bound` (D6(i), residue classes): among the `k` distinct sites of a duplicate-free list some
  class of `(ℤ/(r+1))^d` contains at least `k/(r+1)^d` of them, and distinct sites of one class are at
  `ℓ^∞`-distance `≥ r+1` (`not_withinInf_of_emod`); so the list is all closed with probability
  `≤ ε^{⌈k/(r+1)^d⌉} ≤ θ^k`.
* `sChainsFrom x n`: a finset containing every `*`-path with `n` steps from `x`;
  `card_sChainsFrom_le`: it has at most `(3^d - 1)^n` elements.
* `exists_simple_of_far` (D6(ii)): a closed `*`-path from `x` that leaves `B̄_L(x)` contains (via
  `SimpleGraph.Walk.bypass`) a simple closed `*`-path from `x` with `L` steps.
* `peierlsD`: the union bound `(3^d - 1)^L θ^{L+1} ≤ 2^{-L}`.

Templates: `LQGMetric.perc_list_bound`, `LQGMetric.percFar_of_emod`, `LQGMetric.card_percChainsFrom_le`,
`LQGMetric.percBadTB_exists_list` (`lqg_metric/LQGMetric/Perc/{Peierls,Paths}.lean`, planar case),
generalized to `ℤ^d`.
-/

set_option autoImplicit false

open MeasureTheory Relation
open scoped ENNReal

namespace HigherDimLFPP

namespace Perc

variable {d : ℕ}

/-! ### Residue classes (D6(i)) -/

/-- Distinct sites with the same residues modulo `r + 1` are at `ℓ^∞`-distance `> r`. -/
lemma not_withinInf_of_emod {r : ℕ} {x y : Zd d} (hne : x ≠ y)
    (h : ∀ i, x i % ((r : ℤ) + 1) = y i % ((r : ℤ) + 1)) : ¬ WithinInf (r : ℤ) x y := by
  intro hw
  apply hne
  funext i
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (h i))
  have h2 := hw i
  rw [abs_le] at h2
  have hr : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have hc0 : c = 0 := by
    by_contra hc0
    rcases lt_or_gt_of_ne hc0 with hlt | hgt
    · have : c ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ c := by omega
      nlinarith
  rw [hc0, mul_zero, sub_eq_zero] at hc
  exact hc

/-- **D6(i)**: a fixed duplicate-free list of sites is entirely closed with probability at most
`θ ^ length`. -/
lemma list_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (closed : Zd d → Set Ω) (r : ℕ)
    {ε θ : ℝ≥0∞} (hθ1 : θ ≤ 1) (hεθ : ε ≤ θ ^ ((r + 1) ^ d)) (hε : ∀ x, μ (closed x) ≤ ε)
    (hind : ProductBound μ closed r) (l : List (Zd d)) (hl : l.Nodup) :
    μ {ω | ∀ y ∈ l, ω ∈ closed y} ≤ θ ^ l.length := by
  classical
  set s := l.toFinset with hsdef
  have hs : s.card = l.length := List.toFinset_card_of_nodup hl
  set c : Zd d → Zd d := fun x i => x i % ((r : ℤ) + 1) with hcdef
  set t : Finset (Zd d) := Fintype.piFinset fun _ => Finset.Ico 0 ((r : ℤ) + 1) with htdef
  have hr0 : (0 : ℤ) < (r : ℤ) + 1 := by positivity
  have hct : ∀ x ∈ s, c x ∈ t := by
    intro x _
    simp only [hcdef, htdef, Fintype.mem_piFinset, Finset.mem_Ico]
    exact fun i => ⟨Int.emod_nonneg _ hr0.ne', Int.emod_lt_of_pos _ hr0⟩
  have htcard : t.card = (r + 1) ^ d := by
    rw [htdef, Fintype.card_piFinset, Int.card_Ico]
    have : ((r : ℤ) + 1 - 0).toNat = r + 1 := by omega
    rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have htne : t.Nonempty := ⟨0, by simp [htdef]⟩
  obtain ⟨z, -, hz⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hct htne
    (b := (l.length : ℚ) / ((r + 1) ^ d : ℚ)) (by
      rw [htcard, nsmul_eq_mul, hs]
      push_cast
      rw [mul_div_cancel₀]
      positivity)
  set F := s.filter (fun x => c x = z) with hFdef
  have hm : l.length ≤ (r + 1) ^ d * F.card := by
    rw [div_le_iff₀ (by positivity)] at hz
    exact_mod_cast (by linarith : (l.length : ℚ) ≤ (r + 1) ^ d * (F.card : ℚ))
  have hFs : ∀ x ∈ F, x ∈ l := fun x hx =>
    List.mem_toFinset.mp (Finset.mem_filter.mp hx).1
  calc μ {ω | ∀ y ∈ l, ω ∈ closed y} ≤ μ (⋂ x ∈ F, closed x) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_iInter]
        exact fun x hx => hω x (hFs x hx)
    _ ≤ ∏ x ∈ F, μ (closed x) := by
        refine hind F fun x hx y hy hxy => ?_
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        rw [← hy'] at hx'
        exact not_withinInf_of_emod hxy fun i => congrFun hx' i
    _ ≤ ε ^ F.card := Finset.prod_le_pow_card _ _ _ fun x _ => hε x
    _ ≤ (θ ^ ((r + 1) ^ d)) ^ F.card := pow_le_pow_left₀ bot_le hεθ _
    _ = θ ^ ((r + 1) ^ d * F.card) := (pow_mul _ _ _).symm
    _ ≤ θ ^ l.length := pow_le_pow_right_of_le_one' hθ1 hm

/-! ### Counting `*`-paths -/

/-- The `3^d - 1` `*`-neighbours of a site. -/
def sNbrs (x : Zd d) : Finset (Zd d) :=
  ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-1 : ℤ) 1).erase 0).image fun δ => x + δ

lemma card_sNbrs_le (x : Zd d) : (sNbrs x).card ≤ 3 ^ d - 1 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_erase_of_mem (by simp), Fintype.card_piFinset, Int.card_Icc]
  simp

lemma mem_sNbrs {x y : Zd d} (h : SAdj x y) : y ∈ sNbrs x := by
  refine Finset.mem_image.mpr ⟨y - x, ?_, by simp⟩
  refine Finset.mem_erase.mpr ⟨sub_ne_zero.mpr h.ne.symm, ?_⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have := h.2 i
  rw [abs_le] at this
  simp only [Pi.sub_apply]
  constructor <;> omega

/-- A finset containing all `*`-paths with `n` steps started at `x`. -/
def sChainsFrom : Zd d → ℕ → Finset (List (Zd d))
  | x, 0 => {[x]}
  | x, n + 1 => (sNbrs x).biUnion fun y => (sChainsFrom y n).image (List.cons x)

lemma card_sChainsFrom_le (x : Zd d) (n : ℕ) : (sChainsFrom x n).card ≤ (3 ^ d - 1) ^ n := by
  induction n generalizing x with
  | zero => simp [sChainsFrom]
  | succ n ih =>
    simp only [sChainsFrom]
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ y ∈ sNbrs x, ((sChainsFrom y n).image (List.cons x)).card
        ≤ ∑ _y ∈ sNbrs x, (3 ^ d - 1) ^ n :=
          Finset.sum_le_sum fun y _ => (Finset.card_image_le).trans (ih y)
      _ = (sNbrs x).card * (3 ^ d - 1) ^ n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (3 ^ d - 1) * (3 ^ d - 1) ^ n := Nat.mul_le_mul_right _ (card_sNbrs_le x)
      _ = (3 ^ d - 1) ^ (n + 1) := (pow_succ' _ n).symm

lemma mem_sChainsFrom (n : ℕ) : ∀ (x : Zd d) (t : List (Zd d)),
    (x :: t).IsChain SAdj → t.length = n → x :: t ∈ sChainsFrom x n := by
  induction n with
  | zero =>
    intro x t _ ht
    rw [List.length_eq_zero_iff] at ht
    subst ht
    simp [sChainsFrom]
  | succ n ih =>
    intro x t hc ht
    obtain ⟨y, t', rfl⟩ : ∃ y t', t = y :: t' := by
      cases t with
      | nil => simp at ht
      | cons y t' => exact ⟨y, t', rfl⟩
    rw [List.isChain_cons_cons] at hc
    simp only [sChainsFrom, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨y, mem_sNbrs hc.1, y :: t', ih y t' hc.2 (by simpa using ht), rfl⟩

lemma length_of_mem_sChainsFrom (n : ℕ) : ∀ (x : Zd d) (l : List (Zd d)),
    l ∈ sChainsFrom x n → l.length = n + 1 := by
  induction n with
  | zero => intro x l hl; simp [sChainsFrom] at hl; simp [hl]
  | succ n ih =>
    intro x l hl
    simp only [sChainsFrom, Finset.mem_biUnion, Finset.mem_image] at hl
    obtain ⟨y, -, t, ht, rfl⟩ := hl
    simp [ih y t ht]

/-! ### Simple paths (D6(ii)) -/

lemma isChain_and_of_forall {R : Zd d → Zd d → Prop} {P : Zd d → Prop} :
    ∀ {l : List (Zd d)}, l.IsChain R → (∀ z ∈ l, P z) → l.IsChain (fun a b => R a b ∧ P a ∧ P b)
  | [], _, _ => .nil
  | [_], _, _ => .singleton _
  | a :: b :: t, h, hP => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨⟨h.1, hP a (by simp), hP b (by simp)⟩,
      isChain_and_of_forall h.2 fun z hz => hP z (List.mem_cons_of_mem _ hz)⟩

/-- Every site of a walk satisfies `P` if its start does and every edge joins sites satisfying `P`. -/
lemma walk_support_forall {G : SimpleGraph (Zd d)} {P : Zd d → Prop}
    (hG : ∀ {a b}, G.Adj a b → P a ∧ P b) :
    ∀ {u v : Zd d} (w : G.Walk u v), P u → ∀ z ∈ w.support, P z := by
  intro u v w
  induction w with
  | nil => intro hu z hz; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ hu
  | @cons a b c h w ih =>
    intro ha z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih (hG h).2 z hz

/-- A walk of length `n` for `*`-adjacency ends within `ℓ^∞`-distance `n` of its start. -/
lemma walk_withinInf {G : SimpleGraph (Zd d)} (hG : ∀ {a b}, G.Adj a b → SAdj a b) :
    ∀ {u v : Zd d} (w : G.Walk u v), WithinInf (w.length : ℤ) v u := by
  intro u v w
  induction w with
  | nil => exact withinInf_refl (by simp) _
  | @cons a b c h w ih =>
    have := ih.trans (hG h).symm.withinInf
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    exact this

/-- A `*`-path from `x` whose sites satisfy `P` and which leaves `B̄_L(x)` contains a simple one with
exactly `L` steps. -/
lemma exists_simple_of_far {P : Zd d → Prop} {x : Zd d} {L : ℕ} {γ : List (Zd d)}
    (hhead : γ.head? = some x) (hchain : γ.IsChain SAdj) (hP : ∀ y ∈ γ, P y)
    {y : Zd d} (hyγ : y ∈ γ) (hy : ¬ WithinInf (L : ℤ) y x) :
    ∃ t : List (Zd d), (x :: t).Nodup ∧ (x :: t).IsChain SAdj ∧ (∀ z ∈ x :: t, P z) ∧
      t.length = L := by
  classical
  set rel : Zd d → Zd d → Prop := fun a b => SAdj a b ∧ P a ∧ P b with hrel
  set G : SimpleGraph (Zd d) := SimpleGraph.fromRel rel with hG
  have hGadj : ∀ {a b}, G.Adj a b → rel a b := by
    intro a b h
    rw [hG, SimpleGraph.fromRel_adj] at h
    rcases h.2 with h' | h'
    · exact h'
    · exact ⟨h'.1.symm, h'.2.2, h'.2.1⟩
  have hrelG : ∀ {a b}, rel a b → G.Adj a b := by
    intro a b h
    rw [hG, SimpleGraph.fromRel_adj]
    exact ⟨h.1.ne, Or.inl h⟩
  -- reachability inside the closed sites
  have hchain' : γ.IsChain rel := isChain_and_of_forall hchain hP
  have hreach : ReflTransGen rel x y := by
    obtain ⟨a, t, rfl⟩ : ∃ a t, γ = a :: t := by
      cases γ with
      | nil => simp at hhead
      | cons a t => exact ⟨a, t, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    exact List.IsChain.induction (fun z => ReflTransGen rel a z) (a :: t) hchain'
      (fun _ _ hab hxa => hxa.tail hab) (fun _ => ReflTransGen.refl) y hyγ
  have hR : G.Reachable x y := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    exact ReflTransGen.mono (fun a b (h : rel a b) => hrelG h) x y hreach
  obtain ⟨p⟩ := hR
  set q := p.bypass with hq
  have hpath : q.IsPath := p.bypass_isPath
  -- facts on the support of `q`
  have hsupp_chain : q.support.IsChain SAdj := q.isChain_adj_support.imp fun _ _ h => (hGadj h).1
  have hx : P x := by
    obtain ⟨a, t, rfl⟩ : ∃ a t, γ = a :: t := by
      cases γ with
      | nil => simp at hhead
      | cons a t => exact ⟨a, t, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hhead
    exact hhead ▸ hP a (by simp)
  have hsupp_P : ∀ z ∈ q.support, P z :=
    walk_support_forall (fun h => ⟨(hGadj h).2.1, (hGadj h).2.2⟩) q hx
  have hqlen : L + 1 ≤ q.length := by
    by_contra hlt
    exact hy ((walk_withinInf (fun h => (hGadj h).1) q).mono (by omega))
  -- the first `L` steps
  have hsupp : q.support = x :: q.support.tail := q.cons_tail_support.symm
  refine ⟨q.support.tail.take L, ?_, ?_, ?_, ?_⟩
  · have : x :: q.support.tail.take L = q.support.take (L + 1) := by
      rw [hsupp, List.take_succ_cons]; rfl
    rw [this]
    exact hpath.support_nodup.sublist (List.take_sublist _ _)
  · have : x :: q.support.tail.take L = q.support.take (L + 1) := by
      rw [hsupp, List.take_succ_cons]; rfl
    rw [this]
    exact hsupp_chain.take _
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hsupp_P _ (hsupp ▸ List.mem_cons_self)
    · exact hsupp_P z (List.mem_of_mem_tail (List.mem_of_mem_take hz))
  · rw [List.length_take, List.length_tail, SimpleGraph.Walk.length_support]
    omega

/-! ### The Peierls bound -/

/-- **D6(ii): Peierls bound in `ℤ^d`.** -/
theorem peierlsD (d : ℕ) : PeierlsD d := by
  intro Ω _ μ closed r ε θ hε hind hθ1 hεθ hθ x L
  classical
  set A := (sChainsFrom x L).filter (fun l => l.Nodup) with hA
  have hsub : {ω | ∃ γ : List (Zd d), γ.head? = some x ∧ γ.IsChain SAdj ∧
      (∀ y ∈ γ, ω ∈ closed y) ∧ ∃ y ∈ γ, ¬ WithinInf (L : ℤ) y x} ⊆
      ⋃ l ∈ A, {ω | ∀ y ∈ l, ω ∈ closed y} := by
    intro ω hω
    obtain ⟨γ, hhead, hchain, hcl, y, hyγ, hy⟩ := hω
    obtain ⟨t, hnd, hch, hcl', ht⟩ :=
      exists_simple_of_far (P := fun z => ω ∈ closed z) hhead hchain hcl hyγ hy
    simp only [Set.mem_iUnion]
    exact ⟨x :: t, Finset.mem_filter.mpr ⟨mem_sChainsFrom L x t hch ht, hnd⟩, hcl'⟩
  calc μ {ω | ∃ γ : List (Zd d), γ.head? = some x ∧ γ.IsChain SAdj ∧
        (∀ y ∈ γ, ω ∈ closed y) ∧ ∃ y ∈ γ, ¬ WithinInf (L : ℤ) y x}
      ≤ μ (⋃ l ∈ A, {ω | ∀ y ∈ l, ω ∈ closed y}) := measure_mono hsub
    _ ≤ ∑ l ∈ A, μ {ω | ∀ y ∈ l, ω ∈ closed y} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _l ∈ A, θ ^ (L + 1) := by
        refine Finset.sum_le_sum fun l hl => ?_
        obtain ⟨hl1, hl2⟩ := Finset.mem_filter.mp hl
        rw [← length_of_mem_sChainsFrom L x l hl1]
        exact list_bound μ closed r hθ1 hεθ hε hind l hl2
    _ = A.card * θ ^ (L + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((3 : ℝ≥0∞) ^ d) ^ L * θ ^ (L + 1) := by
        gcongr
        have h1 : A.card ≤ (3 ^ d) ^ L :=
          (Finset.card_filter_le _ _).trans ((card_sChainsFrom_le x L).trans
            (Nat.pow_le_pow_left (Nat.sub_le _ _) L))
        exact_mod_cast h1
    _ = ((3 : ℝ≥0∞) ^ d * θ) ^ L * θ := by rw [mul_pow, pow_succ]; ring
    _ ≤ 2⁻¹ ^ L * 1 := by gcongr
    _ = 2⁻¹ ^ L := mul_one _

end Perc

end HigherDimLFPP
