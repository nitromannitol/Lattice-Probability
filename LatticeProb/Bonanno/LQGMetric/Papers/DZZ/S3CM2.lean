/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Meas
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4Fine
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Cor33
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas

/-!
# DZZ (eq-very-crude-prime): deterministic facts about `D'` (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 849–853): the crude bound on `log D'` comes from the
size of the minimal cell. Deterministic inputs (own elementary arguments; DZZ omit them):

* `approxDistSet_toNat_le`: if every box of level `k` has mass `< δ²` (so all cells have level
  `≤ k`), then `D'(A, B) ≤ (k+1) 4^k` whenever it is finite (a geodesic visits distinct cells);
* `approxDistSet_le_iff`: `D'(A, B) ≤ K` iff some chain of at most `K` neighbouring cells joins a
  box meeting `A` to a box meeting `B`;
* `measurable_logApproxLGD`: `ω ↦ log D'_{γ,δ}(A, B)` is measurable, for arbitrary sets `A, B`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

section Det

variable (m : DyBox → ℝ) (δ : ℝ)

/-- all vertices of a walk of the cell graph starting at a cell are cells -/
lemma cm_walk_support_isCell {b b' : DyBox} (p : (cellGraph m δ).Walk b b')
    (hb : IsCell m δ b) : ∀ c ∈ p.support, IsCell m δ c := by
  induction p with
  | nil => intro c hc; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hc
           exact hc ▸ hb
  | cons h q ih =>
    intro c hc
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.1
    · exact ih h.2.1 c hc

/-- an infimum in `ℕ∞` below a natural number is attained -/
lemma cm_iInf_le_nat {ι : Sort*} {f : ι → ℕ∞} {K : ℕ} (h : (⨅ i, f i) ≤ K) : ∃ i, f i ≤ K := by
  by_contra hne
  push Not at hne
  have : ((K + 1 : ℕ) : ℕ∞) ≤ ⨅ i, f i := le_iInf fun i => by
    have := hne i
    exact_mod_cast Order.add_one_le_of_lt this
  have := this.trans h
  norm_cast at this
  omega

/-- the level-bounded boxes inject into `ℕ × ℕ × ℕ` with `n ≤ k`, `j, k' < 2^k` -/
lemma cm_card_le {k : ℕ} (l : List DyBox) (hl : l.Nodup) (hk : ∀ c ∈ l, c.n ≤ k) :
    l.length ≤ (k + 1) * 2 ^ k * 2 ^ k := by
  set g : DyBox → ℕ × ℕ × ℕ := fun b => (b.n, b.j, b.k)
  have hg : Function.Injective g := by
    rintro ⟨n, j, k, _, _⟩ ⟨n', j', k', _, _⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  have hnd : (l.map g).Nodup := hl.map hg
  have hsub : (l.map g).toFinset ⊆
      Finset.range (k + 1) ×ˢ Finset.range (2 ^ k) ×ˢ Finset.range (2 ^ k) := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have h1 := hk c hc
    have h2 : 2 ^ c.n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h1
    simp only [g, Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by have := c.hj; omega, by have := c.hk; omega⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_product,
    Finset.card_product, Finset.card_range, Finset.card_range] at this
  rw [mul_assoc]; exact this

/-- **`D' ≤ (k+1) 4^k`** when every box of level `k` has mass `< δ²` -/
theorem approxDist_le_of_level {k : ℕ} (hk : ∀ b : DyBox, b.n = k → m b < δ ^ 2) {x y : ℂ}
    (hfin : approxDist m δ x y ≠ ⊤) :
    approxDist m δ x y ≤ ((k + 1) * 2 ^ k * 2 ^ k : ℕ) := by
  have hlt := lt_top_iff_ne_top.2 hfin
  simp only [approxDist, iInf_lt_iff] at hlt
  obtain ⟨b, b', ⟨hb, hbx⟩, ⟨hb', hby⟩, hlt⟩ := hlt
  have hne : (cellGraph m δ).edist b b' ≠ ⊤ := by
    intro h; rw [h, top_add] at hlt; exact lt_irrefl _ hlt
  obtain ⟨p, -⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  set q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hcells := cm_walk_support_isCell m δ q hb
  have hlen := cm_card_le q.support hq.support_nodup fun c hc =>
    IsCell.n_le_of_level hk (hcells c hc)
  rw [SimpleGraph.Walk.length_support] at hlen
  refine (iInf₂_le_of_le b b' (iInf₂_le_of_le ⟨hb, hbx⟩ ⟨hb', hby⟩ le_rfl)).trans ?_
  refine (add_le_add (SimpleGraph.Walk.edist_le q) le_rfl).trans ?_
  exact_mod_cast hlen

/-- **`D'(A, B) ≤ (k+1) 4^k`** (as a natural number) when every box of level `k` has mass
`< δ²` -/
theorem approxDistSet_toNat_le {k : ℕ} (hk : ∀ b : DyBox, b.n = k → m b < δ ^ 2)
    (A B : Set ℂ) : (approxDistSet m δ A B).toNat ≤ (k + 1) * 2 ^ k * 2 ^ k := by
  by_cases hfin : approxDistSet m δ A B = ⊤
  · rw [hfin]; simp
  have hlt := lt_top_iff_ne_top.2 hfin
  simp only [approxDistSet, iInf_lt_iff] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := hlt
  have h1 : approxDistSet m δ A B ≤ ((k + 1) * 2 ^ k * 2 ^ k : ℕ) :=
    (iInf₂_le_of_le x hx (iInf₂_le_of_le y hy le_rfl)).trans
      (approxDist_le_of_level m δ hk hxy.ne)
  exact ENat.toNat_le_of_le_natCast h1

/-- a chain of neighbouring cells from `b` to `b'` bounds the graph distance -/
lemma cm_edist_le_of_chain : ∀ (l : List DyBox) (b b' : DyBox), l.head? = some b →
    l.getLast? = some b' → l.IsChain Neighbour → (∀ c ∈ l, IsCell m δ c) →
    (cellGraph m δ).edist b b' + 1 ≤ l.length
  | [], _, _, h, _, _, _ => by simp at h
  | [a], b, b', h1, h2, _, _ => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    subst h1; subst h2
    simp
  | a :: c :: t, b, b', h1, h2, hch, hc => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rw [List.isChain_cons_cons] at hch
    have hrec := cm_edist_le_of_chain (c :: t) c b' (by simp)
      (by rw [List.getLast?_cons_cons] at h2; exact h2) hch.2
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    have hadj : (cellGraph m δ).Adj a c :=
      ⟨hc a (by simp), hc c (by simp), hch.1⟩
    have h1 : (cellGraph m δ).edist a c ≤ 1 := (SimpleGraph.edist_eq_one_iff_adj.2 hadj).le
    calc (cellGraph m δ).edist a b' + 1 ≤ ((cellGraph m δ).edist a c +
          (cellGraph m δ).edist c b') + 1 := by gcongr; exact SimpleGraph.edist_triangle
      _ ≤ 1 + (((c :: t).length : ℕ) : ℕ∞) := by
          rw [add_assoc]; exact add_le_add h1 hrec
      _ = ((a :: c :: t).length : ℕ∞) := by
          simp only [List.length_cons]; push_cast; ring

/-- **sublevel sets of `D'(A, B)`** -/
theorem approxDistSet_le_iff (A B : Set ℂ) (K : ℕ) :
    approxDistSet m δ A B ≤ K ↔ ∃ (b b' : DyBox) (l : List DyBox),
      ((∃ x ∈ A, b.Mem x) ∧ (∃ y ∈ B, b'.Mem y) ∧ l.head? = some b ∧ l.getLast? = some b' ∧
        l.IsChain Neighbour ∧ l.length ≤ K) ∧ ∀ c ∈ l, IsCell m δ c := by
  constructor
  · intro h
    obtain ⟨x, h⟩ := cm_iInf_le_nat h
    obtain ⟨hx, h⟩ := cm_iInf_le_nat h
    obtain ⟨y, h⟩ := cm_iInf_le_nat h
    obtain ⟨hy, h⟩ := cm_iInf_le_nat h
    obtain ⟨b, h⟩ := cm_iInf_le_nat h
    obtain ⟨b', h⟩ := cm_iInf_le_nat h
    obtain ⟨⟨hb, hbx⟩, h⟩ := cm_iInf_le_nat h
    obtain ⟨⟨hb', hby⟩, h⟩ := cm_iInf_le_nat h
    have hne : (cellGraph m δ).edist b b' ≠ ⊤ := by
      intro he; rw [he, top_add] at h; exact absurd h (by simp)
    obtain ⟨p, hp⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
    refine ⟨b, b', p.support, ⟨⟨x, hx, hbx⟩, ⟨y, hy, hby⟩, ?_, ?_, ?_, ?_⟩,
      cm_walk_support_isCell m δ p hb⟩
    · cases p <;> simp
    · rw [List.getLast?_eq_getLast p.support_ne_nil, SimpleGraph.Walk.getLast_support]
    · exact p.isChain_adj_support.imp fun _ _ h => h.2.2
    · rw [SimpleGraph.Walk.length_support]
      rw [← hp] at h
      exact_mod_cast h
  · rintro ⟨b, b', l, ⟨⟨x, hx, hbx⟩, ⟨y, hy, hby⟩, h1, h2, hch, hlen⟩, hc⟩
    have hb : IsCell m δ b := hc b (List.mem_of_mem_head? h1)
    have hb' : IsCell m δ b' := hc b' (List.mem_of_mem_getLast? h2)
    refine (iInf₂_le_of_le x hx (iInf₂_le_of_le y hy (iInf₂_le_of_le b b'
      (iInf₂_le_of_le ⟨hb, hbx⟩ ⟨hb', hby⟩ le_rfl)))).trans ?_
    exact (cm_edist_le_of_chain m δ l b b' h1 h2 hch hc).trans (by exact_mod_cast hlen)

end Det

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **measurability of `D'_{γ,δ}(A, B)`** in `ω`, for arbitrary sets `A, B` -/
theorem measurable_approxLGDSet (hW : IsWhiteNoise P W) (γ δ : ℝ) (A B : Set ℂ) :
    Measurable fun ω => approxLGDSet γ W δ A B ω := by
  refine measurable_enat_of_le fun K => ?_
  simp_rw [approxLGDSet, approxDistSet_le_iff]
  refine measurableSet_setOfPred.2 (Measurable.exists fun b => Measurable.exists fun b' =>
    Measurable.exists fun l => Measurable.and measurable_const
      (Measurable.forall fun c => Measurable.forall fun _ =>
        measurableSet_setOfPred.1 (measurableSet_isCell hW γ δ c)))

/-- **measurability of `log D'_{γ,δ}(A, B)`** -/
theorem measurable_logApproxLGD (hW : IsWhiteNoise P W) (γ δ : ℝ) (A B : Set ℂ) :
    Measurable fun ω => logApproxLGD γ W δ A B ω :=
  measurable_log_toNat.comp (measurable_approxLGDSet hW γ δ A B)

omit [MeasurableSpace Ω] in
lemma logApproxLGD_nonneg (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ) (ω : Ω) :
    0 ≤ logApproxLGD γ W δ A B ω :=
  Real.log_natCast_nonneg _

end DZZ
end LQGMetric
