/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EConn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EBox

/-!
# DDDF Theorem 20, Step 4: the clipped circuit is connected (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105: "gluing the four crossings gives a circuit
in this annulus". For any choice of long crossings `pc e` of the rectangles `e ∈ circR`, the meet
graph on `circR` is connected (`T20E.circR_conn`): each strip's chain is connected
(`hChain_meet`, `vChain_meet`), and the last/first rectangles of a horizontal and a vertical strip
meet at the common corner (`meet_HV`). With the clipping D-DDDF-22 at most one strip of each
direction is missing, so the present strips are still linked. Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

variable {K : ℕ} {pc : Circle × ℂ → ℝ → ℂ}

lemma reach_hChain {V : Set (Circle × ℂ)} (p q : ℤ) (N : ℕ)
    (hV : ∀ n ≤ N, hChain K p q n ∈ V) (hadm : ∀ n ≤ N, LAdm K (hChain K p q n) (pc (hChain K p q n)))
    {n : ℕ} (hn : n ≤ N) : (meetGraph pc V).Reachable (hChain K p q 0) (hChain K p q n) :=
  reach_of_chain (hChain K p q) n (fun k hk => hV k (by omega))
    fun k hk => hChain_meet p q k (hadm k (by omega)) (hadm (k + 1) (by omega))

lemma reach_vChain {V : Set (Circle × ℂ)} (p q : ℤ) (N : ℕ)
    (hV : ∀ n ≤ N, vChain K p q n ∈ V) (hadm : ∀ n ≤ N, LAdm K (vChain K p q n) (pc (vChain K p q n)))
    {n : ℕ} (hn : n ≤ N) : (meetGraph pc V).Reachable (vChain K p q 0) (vChain K p q n) :=
  reach_of_chain (vChain K p q) n (fun k hk => hV k (by omega))
    fun k hk => vChain_meet p q k (hadm k (by omega)) (hadm (k + 1) (by omega))

lemma hChain_last (p q : ℤ) (ℓ : ℕ) :
    hChain K p q (2 * (ℓ - 3)) = eH K (p + (ℓ - 3 : ℕ)) (q + 1) := by
  have : 2 * (ℓ - 3) % 2 = 0 := by omega
  simp only [hChain, this, ite_true]; congr 2; omega

lemma vChain_last (p q : ℤ) (ℓ : ℕ) :
    vChain K p q (2 * (ℓ - 3)) = eV K (p + 2) (q + (ℓ - 3 : ℕ)) := by
  have : 2 * (ℓ - 3) % 2 = 0 := by omega
  simp only [vChain, this, ite_true]; congr 2; omega

lemma adj_reach {V : Set (Circle × ℂ)} {e e' : Circle × ℂ} (he : e ∈ V) (he' : e' ∈ V)
    (h : Meet pc e e') : (meetGraph pc V).Reachable e e' := by
  by_cases hee : e = e'
  · rw [hee]
  · refine SimpleGraph.Adj.reachable ?_
    rw [meetGraph, SimpleGraph.fromRel_adj]
    exact ⟨hee, Or.inl ⟨he, he', h⟩⟩

/-- **The clipped circuit is connected.** -/
theorem circR_conn {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂)
    (hpc : ∀ e ∈ circR K i₁ i₂ j₁ j₂, LAdm K e (pc e)) :
    ∀ e ∈ circR K i₁ i₂ j₁ j₂, ∀ e' ∈ circR K i₁ i₂ j₁ j₂,
      (meetGraph pc (circR K i₁ i₂ j₁ j₂ : Set (Circle × ℂ))).Reachable e e' := by
  classical
  set R := circR K i₁ i₂ j₁ j₂
  set G := meetGraph pc (R : Set (Circle × ℂ))
  obtain ⟨lx3, lxe, lx0, hx1, lx1, hx2⟩ := hx.len
  obtain ⟨ly3, lye, ly0, hy1, ly1, hy2⟩ := hy.len
  have nb := hx.not_both; have nb' := hy.not_both
  set ℓx := (hi K i₂ - lo i₁).toNat
  set ℓy := (hi K j₂ - lo j₁).toNat
  -- membership of the four chains
  have mB : ¬ j₁ < 3 → ∀ n ≤ 2 * (ℓx - 3), hChain K (lo i₁) (j₁ - 3) n ∈ R := fun c n hn => by
    simp only [R, circR, Finset.mem_union, if_neg c]
    exact Or.inl (Or.inl (Or.inl (mem_hSet.2 ⟨n, hn, rfl⟩)))
  have mT : ¬ (2 : ℤ) ^ K < j₂ + 3 → ∀ n ≤ 2 * (ℓx - 3), hChain K (lo i₁) j₂ n ∈ R :=
    fun c n hn => by
    simp only [R, circR, Finset.mem_union, if_neg c]
    exact Or.inl (Or.inl (Or.inr (mem_hSet.2 ⟨n, hn, rfl⟩)))
  have mL : ¬ i₁ < 3 → ∀ n ≤ 2 * (ℓy - 3), vChain K (i₁ - 3) (lo j₁) n ∈ R := fun c n hn => by
    simp only [R, circR, Finset.mem_union, if_neg c]
    exact Or.inl (Or.inr (mem_vSet.2 ⟨n, hn, rfl⟩))
  have mR : ¬ (2 : ℤ) ^ K < i₂ + 3 → ∀ n ≤ 2 * (ℓy - 3), vChain K i₂ (lo j₁) n ∈ R :=
    fun c n hn => by
    simp only [R, circR, Finset.mem_union, if_neg c]
    exact Or.inr (mem_vSet.2 ⟨n, hn, rfl⟩)
  -- reachability inside each chain
  have rB : ∀ (c : ¬ j₁ < 3) n, n ≤ 2 * (ℓx - 3) →
      G.Reachable (hChain K (lo i₁) (j₁ - 3) 0) (hChain K (lo i₁) (j₁ - 3) n) := fun c n hn =>
    reach_hChain _ _ _ (mB c) (fun k hk => hpc _ (mB c k hk)) hn
  have rT : ∀ (c : ¬ (2 : ℤ) ^ K < j₂ + 3) n, n ≤ 2 * (ℓx - 3) →
      G.Reachable (hChain K (lo i₁) j₂ 0) (hChain K (lo i₁) j₂ n) := fun c n hn =>
    reach_hChain _ _ _ (mT c) (fun k hk => hpc _ (mT c k hk)) hn
  have rL : ∀ (c : ¬ i₁ < 3) n, n ≤ 2 * (ℓy - 3) →
      G.Reachable (vChain K (i₁ - 3) (lo j₁) 0) (vChain K (i₁ - 3) (lo j₁) n) := fun c n hn =>
    reach_vChain _ _ _ (mL c) (fun k hk => hpc _ (mL c k hk)) hn
  have rR : ∀ (c : ¬ (2 : ℤ) ^ K < i₂ + 3) n, n ≤ 2 * (ℓy - 3) →
      G.Reachable (vChain K i₂ (lo j₁) 0) (vChain K i₂ (lo j₁) n) := fun c n hn =>
    reach_vChain _ _ _ (mR c) (fun k hk => hpc _ (mR c k hk)) hn
  set fB := hChain K (lo i₁) (j₁ - 3) 0
  set fT := hChain K (lo i₁) j₂ 0
  set fL := vChain K (i₁ - 3) (lo j₁) 0
  set fR := vChain K i₂ (lo j₁) 0
  have h0 : ∀ p q : ℤ, hChain K p q 0 = eH K p (q + 1) := fun p q => by simp [hChain]
  have v0 : ∀ p q : ℤ, vChain K p q 0 = eV K (p + 2) q := fun p q => by simp [vChain]
  have lxN : lo i₁ + ((ℓx - 3 : ℕ) : ℤ) = hi K i₂ - 3 := by push_cast [Nat.cast_sub lx3]; omega
  have lyN : lo j₁ + ((ℓy - 3 : ℕ) : ℤ) = hi K j₂ - 3 := by push_cast [Nat.cast_sub ly3]; omega
  have loi : ¬ i₁ < 3 → lo i₁ = i₁ - 3 := fun c => by simp [lo, c]
  have loj : ¬ j₁ < 3 → lo j₁ = j₁ - 3 := fun c => by simp [lo, c]
  have hii : ¬ (2 : ℤ) ^ K < i₂ + 3 → hi K i₂ = i₂ + 3 := fun c => by simp [hi, c]
  have hij : ¬ (2 : ℤ) ^ K < j₂ + 3 → hi K j₂ = j₂ + 3 := fun c => by simp [hi, c]
  -- the corners
  have cBL : ∀ (c : ¬ j₁ < 3) (c' : ¬ i₁ < 3), G.Reachable fB fL := fun c c' => by
    refine adj_reach (mB c 0 (Nat.zero_le _)) (mL c' 0 (Nat.zero_le _)) ?_
    have a1 := hpc _ (mB c 0 (Nat.zero_le _)); have a2 := hpc _ (mL c' 0 (Nat.zero_le _))
    simp only [fB, fL, h0, v0] at a1 a2 ⊢
    simp only [loi c', loj c] at a1 a2 ⊢
    exact meet_HV (by omega) (by omega) (by omega) (by omega) a1 a2
  have cBR : ∀ (c : ¬ j₁ < 3) (c' : ¬ (2 : ℤ) ^ K < i₂ + 3), G.Reachable fB fR := fun c c' => by
    refine (rB c _ le_rfl).trans (adj_reach (mB c _ le_rfl) (mR c' 0 (Nat.zero_le _)) ?_)
    have a1 := hpc _ (mB c _ le_rfl); have a2 := hpc _ (mR c' 0 (Nat.zero_le _))
    simp only [fR, hChain_last, v0, lxN] at a1 a2 ⊢
    simp only [hii c', loj c] at a1 a2 ⊢
    exact meet_HV (by omega) (by omega) (by omega) (by omega) a1 a2
  have cTL : ∀ (c : ¬ (2 : ℤ) ^ K < j₂ + 3) (c' : ¬ i₁ < 3), G.Reachable fT fL := fun c c' => by
    refine (adj_reach (mT c 0 (Nat.zero_le _)) (mL c' _ le_rfl) ?_).trans (rL c' _ le_rfl).symm
    have a1 := hpc _ (mT c 0 (Nat.zero_le _)); have a2 := hpc _ (mL c' _ le_rfl)
    simp only [fT, h0, vChain_last, lyN] at a1 a2 ⊢
    simp only [hij c, loi c'] at a1 a2 ⊢
    exact meet_HV (by omega) (by omega) (by omega) (by omega) a1 a2
  have cTR : ∀ (c : ¬ (2 : ℤ) ^ K < j₂ + 3) (c' : ¬ (2 : ℤ) ^ K < i₂ + 3), G.Reachable fT fR :=
    fun c c' => by
    refine (rT c _ le_rfl).trans ((adj_reach (mT c _ le_rfl) (mR c' _ le_rfl) ?_).trans
      (rR c' _ le_rfl).symm)
    have a1 := hpc _ (mT c _ le_rfl); have a2 := hpc _ (mR c' _ le_rfl)
    simp only [hChain_last, vChain_last, lxN, lyN] at a1 a2 ⊢
    simp only [hij c, hii c'] at a1 a2 ⊢
    exact meet_HV (by omega) (by omega) (by omega) (by omega) a1 a2
  -- a base point: the first rectangle of a present vertical strip
  have hbase : ∃ v, (∀ (c : ¬ j₁ < 3), G.Reachable fB v) ∧
      (∀ (c : ¬ (2 : ℤ) ^ K < j₂ + 3), G.Reachable fT v) ∧
      (∀ (c : ¬ i₁ < 3), G.Reachable fL v) ∧ (∀ (c : ¬ (2 : ℤ) ^ K < i₂ + 3), G.Reachable fR v) := by
    by_cases cL : i₁ < 3
    · have cR : ¬ (2 : ℤ) ^ K < i₂ + 3 := fun h => nb ⟨cL, h⟩
      refine ⟨fR, fun c => cBR c cR, fun c => cTR c cR, fun c => absurd cL c,
        fun _ => SimpleGraph.Reachable.refl _⟩
    · refine ⟨fL, fun c => cBL c cL, fun c => cTL c cL, fun _ => SimpleGraph.Reachable.refl _,
        fun c' => ?_⟩
      by_cases cD : j₁ < 3
      · have cU : ¬ (2 : ℤ) ^ K < j₂ + 3 := fun h => nb' ⟨cD, h⟩
        exact (cTR cU c').symm.trans (cTL cU cL)
      · exact (cBR cD c').symm.trans (cBL cD cL)
  obtain ⟨v, vB, vT, vL, vR⟩ := hbase
  have key : ∀ e ∈ R, G.Reachable e v := by
    intro e he
    rcases circR_cases he with ⟨c, h⟩ | ⟨c, h⟩ | ⟨c, h⟩ | ⟨c, h⟩
    · obtain ⟨n, hn, rfl⟩ := mem_hSet.1 h; exact (rB c n hn).symm.trans (vB c)
    · obtain ⟨n, hn, rfl⟩ := mem_hSet.1 h; exact (rT c n hn).symm.trans (vT c)
    · obtain ⟨n, hn, rfl⟩ := mem_vSet.1 h; exact (rL c n hn).symm.trans (vL c)
    · obtain ⟨n, hn, rfl⟩ := mem_vSet.1 h; exact (rR c n hn).symm.trans (vR c)
  exact fun e he e' he' => (key e he).trans (key e' he').symm

end T20E
end DDDF
end LQGMetric
