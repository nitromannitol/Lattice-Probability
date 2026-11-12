/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32K1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9D

/-!
# Walled P3.2, K1: the approximate distance through the cells meeting a wall set (P2-DZZ317K)

Decision D117 (`decisions/DEC-117.md` §3, route R2; DZZ Remark 5.2, arXiv:1807.00422,
`LBM_LGDarXiv.tex` l. 2281–2284). DZZ's `D'_{γ,δ}` (l. 787–790) is the graph distance of the cells
of `𝒱_δ`; its walled analogue for a closed set `K` uses only the cells *meeting* `K`.

* `cellGraphOn S m δ`, `approxDistOn S m δ`, `approxDistSetOn S m δ`: the cell graph and `D'`
  restricted to a family `S` of dyadic boxes (generic, deterministic);
* `approxLGDOn S`, `approxLGDSetOn S`: `D'` through a cell family `S` (the walled statements of
  S3P32K3–S3P317E are generic in `S`);
* `cellsMeeting K`, **`approxLGDIn K`**, **`approxLGDSetIn K`**: the walled `D'` of D117
  (`S = cellsMeeting K`);
* `approxDistSet_le_approxDistSetOn`, `approxLGDSet_le_approxLGDSetOn`: restricting the cells only
  increases `D'`;
* `approxDistOn_le_card_of_path`: the count of a crossing (`approxDist_le_card_of_path`, S3L5XCell)
  for the restricted graph (the walk is transferred to the subgraph);
* **`approxDistOn_le_four_mul_lgd`**: DZZ l. 1166–1167 for the walled measure: on
  (eq-Euclidean-Ball-covering), `D'^K_{δ'}(u,v) ≤ 4 D^K_δ(u,v)` (the 4 cells covering a ball inside
  `K` meet `K`, so the cell chain of the proof `approxDist_le_four_mul_of_path`, S3P32W3, uses only
  cells meeting `K`);
* **`l32BallCoverIn_dzzMuIn`**: the lower-half input of the walled P3.2,
  `L32BallCoverIn P γ W K (dzzWall K μIn)`, unconditional, from the proved
  (eq-Euclidean-Ball-covering) at `μIn` (P2-DZZETA2, S3Eta9D) and Lemma 3.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

section Restricted

variable (S : Set DyBox) (m : DyBox → ℝ) (δ : ℝ)

/-- The cell graph of `𝒱_δ` restricted to the boxes of `S`. -/
def cellGraphOn : SimpleGraph DyBox where
  Adj b b' := (cellGraph m δ).Adj b b' ∧ b ∈ S ∧ b' ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.2.2.1 rfl⟩

lemma cellGraphOn_le : cellGraphOn S m δ ≤ cellGraph m δ := fun _ _ h => h.1

/-- `D'_δ(u, v)` through the cells of `S` only. -/
def approxDistOn (u v : ℂ) : ℕ∞ :=
  ⨅ (b : DyBox) (b' : DyBox) (_ : IsCell m δ b ∧ b.Mem u ∧ b ∈ S)
    (_ : IsCell m δ b' ∧ b'.Mem v ∧ b' ∈ S), (cellGraphOn S m δ).edist b b' + 1

/-- `min_{x ∈ A, y ∈ B}` of `approxDistOn`. -/
def approxDistSetOn (A B : Set ℂ) : ℕ∞ := ⨅ x ∈ A, ⨅ y ∈ B, approxDistOn S m δ x y

lemma approxDist_le_approxDistOn (u v : ℂ) : approxDist m δ u v ≤ approxDistOn S m δ u v := by
  unfold approxDist approxDistOn
  refine le_iInf fun b => le_iInf fun b' => le_iInf fun hb => le_iInf fun hb' => ?_
  refine iInf_le_of_le b (iInf_le_of_le b' (iInf_le_of_le ⟨hb.1, hb.2.1⟩
    (iInf_le_of_le ⟨hb'.1, hb'.2.1⟩ ?_)))
  gcongr
  exact cellGraphOn_le S m δ

lemma approxDistSet_le_approxDistSetOn (A B : Set ℂ) :
    approxDistSet m δ A B ≤ approxDistSetOn S m δ A B :=
  iInf₂_mono fun x _ => iInf₂_mono fun y _ => approxDist_le_approxDistOn S m δ x y

end Restricted

/-- The dyadic boxes whose closure meets `K`. -/
def cellsMeeting (K : Set ℂ) : Set DyBox := {b | (b.closedBox ∩ K).Nonempty}

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `D'_{γ,δ}(u, v)` through the cells of a family `S` only. -/
def approxLGDOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (u v : ℂ) (ω : Ω) : ℕ∞ :=
  approxDistOn S (approxLQG γ W ω) δ u v

/-- `min_{x ∈ A, y ∈ B}` of `approxLGDOn S`. -/
def approxLGDSetOn (S : Set DyBox) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ)
    (ω : Ω) : ℕ∞ :=
  approxDistSetOn S (approxLQG γ W ω) δ A B

/-- **The walled approximate distance** `D'^K_{γ,δ}(u, v)` (D117 §3): cell-graph distance through
the cells of `𝒱_δ` meeting `K`. -/
def approxLGDIn (K : Set ℂ) (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (u v : ℂ) (ω : Ω) : ℕ∞ :=
  approxLGDOn (cellsMeeting K) γ W δ u v ω

section Count

variable {m : DyBox → ℝ} {δ : ℝ}

/-- A walk whose support lies in a finite set bounds the graph distance (any graph). -/
lemma edist_add_one_le_card_gen {G : SimpleGraph DyBox} {T T' : DyBox} (w : G.Walk T T')
    (S : Finset DyBox) (hw : ∀ x ∈ w.support, x ∈ S) : G.edist T T' + 1 ≤ (S.card : ℕ∞) := by
  classical
  set q := w.toPath with hq
  have hsub : ∀ x ∈ (q : G.Walk T T').support, x ∈ S := fun x hx =>
    hw x (SimpleGraph.Walk.support_toPath_subset_support w hx)
  have hnd := q.2.support_nodup
  have hlen : (q : G.Walk T T').support.length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun x hx => hsub x (List.mem_toFinset.1 hx)
  rw [SimpleGraph.Walk.length_support] at hlen
  calc G.edist T T' + 1 ≤ ((q : G.Walk T T').length : ℕ∞) + 1 := by
        gcongr; exact SimpleGraph.edist_le _
    _ = (((q : G.Walk T T').length + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ (S.card : ℕ∞) := by exact_mod_cast hlen

/-- **The count of a crossing, restricted cells**: as `approxDist_le_card_of_path` (S3L5XCell),
when the cells of the path all lie in `Sf ⊆ S`. -/
theorem approxDistOn_le_card_of_path (S : Set DyBox)
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ b → b.n ≤ N₀) (p : ℕ → DyBox) (M : ℕ) (hpn : ∀ t ≤ M, N₀ ≤ (p t).n)
    (hstep : ∀ t < M, p t = p (t + 1) ∨ SqAdj (p t) (p (t + 1))) (Sf : Finset DyBox)
    (hSf : ∀ T ∈ Sf, T ∈ S)
    (hS : ∀ t ≤ M, ∀ T, IsSqCell m δ (p t) T → T ∈ Sf) {u v : ℂ}
    (hu0 : (p 0).Mem u) (hvM : (p M).Mem v) : approxDistOn S m δ u v ≤ (Sf.card : ℕ∞) := by
  obtain ⟨T₀, h₀⟩ := exists_isSqCell hpart hN₀ (hpn 0 (Nat.zero_le _))
  obtain ⟨T₁, h₁⟩ := exists_isSqCell hpart hN₀ (hpn M le_rfl)
  obtain ⟨w, hw⟩ := exists_walk_of_path hpart hN₀ p M hpn hstep Sf hS h₀ M le_rfl T₁ h₁
  have hT₀ : T₀.Mem u := by
    have := mem_anc hu0 h₀.2.1; rwa [h₀.2.2] at this
  have hT₁ : T₁.Mem v := by
    have := mem_anc hvM h₁.2.1; rwa [h₁.2.2] at this
  have hedge : ∀ e, e ∈ w.edges → e ∈ (cellGraphOn S m δ).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      exact ⟨w.adj_of_mem_edges he, hSf _ (hw _ (w.fst_mem_support_of_mem_edges he)),
        hSf _ (hw _ (w.snd_mem_support_of_mem_edges he))⟩
  set w' := w.transfer (cellGraphOn S m δ) hedge
  have hw' : ∀ x ∈ w'.support, x ∈ Sf := by
    intro x hx
    rw [SimpleGraph.Walk.support_transfer] at hx
    exact hw x hx
  unfold approxDistOn
  refine (iInf_le_of_le T₀ (iInf_le_of_le T₁ (iInf_le_of_le
    (show IsCell m δ _ ∧ _ ∧ _ from ⟨h₀.1, hT₀, hSf _ (hS 0 (Nat.zero_le _) _ h₀)⟩)
    (iInf_le_of_le (show IsCell m δ _ ∧ _ ∧ _ from ⟨h₁.1, hT₁, hSf _ (hS M le_rfl _ h₁)⟩)
      le_rfl)))).trans ?_
  exact edist_add_one_le_card_gen w' Sf hw'

end Count

end DZZ
end LQGMetric
