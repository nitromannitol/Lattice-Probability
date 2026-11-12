/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412dUniq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412dArc

/-!
# GM L4.14′, repaired proof (DEC-86 (1)): uniqueness of `α_B`, maximal arcs meet

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.14
(`lem-dc-set`, l. 2482 and l. 2504–2518), as repaired in DEC-86 (decisions/DEC-86.md, item (1),
"Radius choice" and "Step 2").

* `p412d_shadow_arc` — (S) for an arc: `y ∉ ∂B` with (LC) is not in `cl U(α) ∩ cl W(α)`.
* `p412d_unique` — (replaces l. 2482) at most one arc `α ⊆ cl N(B)` of `∂B ∖ K` has
  `y ∈ cl U(α)` when `y ∉ ∂B`.
* `p412d_max_meet` — (Step 2, l. 2504–2518 with closures) the closures of two arcs whose bounded
  sides are maximal (for inclusion) and both contain `y` in their closures intersect.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut

namespace LQGMetric.GM

theorem p412d_dgW_unbdd {F : Set ℂ} (h : (dgW F).Nonempty) : ¬ IsBounded (dgW F) := by
  obtain ⟨x, hx⟩ := h
  exact fun hb => hx.2 (hb.subset (p412d_sub_dgW isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) (mem_connectedComponentIn hx.1) hx))

/-- **(S) for an arc.** -/
theorem p412d_shadow_arc {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c y₀ y : ℂ} {r : ℝ} (hr : 0 < r) (hy₀ : y₀ ∈ sphere c r)
    (hy₀K : y₀ ∉ K) (hyS : y ∉ sphere c r) (hLC : LocConnAt K y)
    (hB : y ∈ closure (dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K)))
    (hW : y ∈ closure (dgW (connectedComponentIn (sphere c r \ K) y₀ ∪ K))) : False := by
  obtain ⟨u, w, hBu, hWw, -, -⟩ := p412d_arc hK hKc hKo hr hy₀ hy₀K
  have hyα : y ∉ closure (connectedComponentIn (sphere c r \ K) y₀) := fun h =>
    hyS ((isClosed_sphere.closure_subset_iff.2 (cc_subset_sphere K c y₀ r)) h)
  rw [hBu] at hB
  rw [hWw] at hW
  have heq := p412c_shadow hLC hyα hB hW
  rw [← hBu, ← hWw] at heq
  have hBe : dgB (connectedComponentIn (sphere c r \ K) y₀ ∪ K) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx =>
      disjoint_left.1 (p412d_dgB_dgW_disj _) hx (heq ▸ hx)
  rw [hBu.symm.trans hBe, closure_empty] at hB
  exact hB

/-- **Uniqueness of `α_B`** (DEC-86 (1), radius choice; replaces GM l. 2482). -/
theorem p412d_unique {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c y₁ y₂ y : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₁ : y₁ ∈ sphere c r) (hy₁K : y₁ ∉ K) (hy₂ : y₂ ∈ sphere c r) (hy₂K : y₂ ∉ K)
    (h₁N : connectedComponentIn (sphere c r \ K) y₁ ⊆ closure (dgW (closedBall c r ∪ K)))
    (h₂N : connectedComponentIn (sphere c r \ K) y₂ ⊆ closure (dgW (closedBall c r ∪ K)))
    (hyS : y ∉ sphere c r) (hLC : LocConnAt K y)
    (h₁ : y ∈ closure (dgB (connectedComponentIn (sphere c r \ K) y₁ ∪ K)))
    (h₂ : y ∈ closure (dgB (connectedComponentIn (sphere c r \ K) y₂ ∪ K))) :
    connectedComponentIn (sphere c r \ K) y₁ = connectedComponentIn (sphere c r \ K) y₂ := by
  by_contra hne
  set α₁ := connectedComponentIn (sphere c r \ K) y₁
  set α₂ := connectedComponentIn (sphere c r \ K) y₂
  have hdis : ∀ x ∈ α₁, x ∉ α₂ := fun x hx₁ hx₂ =>
    hne ((connectedComponentIn_eq hx₁).trans (connectedComponentIn_eq hx₂).symm)
  have hKcl := hK.isClosed
  set Fb := closedBall c r ∪ K
  obtain ⟨hNpre, hNu⟩ := p412d_dgW_props (isBounded_closedBall.union hK.isBounded : IsBounded Fb)
  set N := dgW Fb
  have hNout : ∀ z ∈ N, r < dist z c ∧ z ∉ K := fun z hz =>
    ⟨not_le.1 fun h => (p412d_dgW_compl Fb hz) (Or.inl h),
      fun h => (p412d_dgW_compl Fb hz) (Or.inr h)⟩
  have hαr : ∀ {y'}, ∀ z ∈ connectedComponentIn (sphere c r \ K) y', dist z c = r :=
    fun z hz => mem_sphere.1 (cc_subset_sphere K c _ r hz)
  have hαK : ∀ {y'}, ∀ z ∈ connectedComponentIn (sphere c r \ K) y', z ∉ K :=
    fun z hz => ((connectedComponentIn_subset _ _) hz).2
  have hNF : ∀ {y'}, N ⊆ (connectedComponentIn (sphere c r \ K) y' ∪ K)ᶜ := by
    rintro y' z hzN (h | h)
    · linarith [hαr z h, (hNout z hzN).1]
    · exact (hNout z hzN).2 h
  have hNW₂ : N ⊆ dgW (α₂ ∪ K) := p412d_sub_dgW_of_unbdd hNpre hNF hNu
  obtain ⟨u₂, w₂, hB₂, -, hα₂B, -⟩ := p412d_arc hK hKc hKo hr hy₂ hy₂K
  have hB₂o : IsOpen (dgB (α₂ ∪ K)) := p412d_isOpen_dgB (isClosed_cc_union K hKcl c y₂ r)
  -- `U(α₂)` misses `α₁ ⊆ cl N ⊆ cl W(α₂)`
  have hB₂α₁ : ∀ x ∈ dgB (α₂ ∪ K), x ∉ α₁ := fun x hxB hxα => by
    obtain ⟨z, hzB, hzN⟩ := mem_closure_iff.1 (h₁N hxα) _ hB₂o hxB
    exact disjoint_left.1 (p412d_dgB_dgW_disj _) hzB (hNW₂ hzN)
  -- `U(α₂) ∪ α₂ ∪ N` is preconnected, unbounded, and misses `α₁ ∪ K`
  have hy₂α : y₂ ∈ α₂ := mem_connectedComponentIn ⟨hy₂, hy₂K⟩
  have hP1 : IsPreconnected (dgB (α₂ ∪ K) ∪ α₂) := by
    have h := (isPreconnected_connectedComponentIn (F := (α₂ ∪ K)ᶜ) (x := u₂))
    rw [← hB₂] at h
    exact h.subset_closure subset_union_left (union_subset subset_closure hα₂B)
  have hP2 : IsPreconnected (α₂ ∪ N) :=
    hNpre.subset_closure subset_union_right (union_subset h₂N subset_closure)
  have hP := hP1.union y₂ (Or.inr hy₂α) (Or.inl hy₂α) hP2
  have hPF : (dgB (α₂ ∪ K) ∪ α₂) ∪ (α₂ ∪ N) ⊆ (α₁ ∪ K)ᶜ := by
    rintro z ((hz | hz) | (hz | hz)) (h | h)
    · exact hB₂α₁ z hz h
    · exact hz.1 (Or.inr h)
    · exact hdis z h hz
    · exact hαK z hz h
    · exact hdis z h hz
    · exact hαK z hz h
    · exact (hNF (y' := y₁)) hz (Or.inl h)
    · exact (hNF (y' := y₁)) hz (Or.inr h)
  have hPW := p412d_sub_dgW_of_unbdd hP hPF fun hb => hNu (hb.subset fun z hz => Or.inr (Or.inr hz))
  have hyW : y ∈ closure (dgW (α₁ ∪ K)) :=
    closure_mono (fun z hz => hPW (Or.inl (Or.inl hz))) h₂
  exact p412d_shadow_arc hK hKc hKo hr hy₁ hy₁K hyS hLC h₁ hyW

/-- Step 2, auxiliary: `α₁ ⊆ U(α₂)` and maximality of `U(α₁)` are incompatible. -/
theorem p412d_max_aux {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c₁ c₂ y₁ y₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hy₁ : y₁ ∈ sphere c₁ r₁) (hy₁K : y₁ ∉ K) (hy₂ : y₂ ∈ sphere c₂ r₂) (hy₂K : y₂ ∉ K)
    (hdis : ∀ x ∈ connectedComponentIn (sphere c₁ r₁ \ K) y₁,
      x ∉ connectedComponentIn (sphere c₂ r₂ \ K) y₂)
    (hsub : connectedComponentIn (sphere c₁ r₁ \ K) y₁ ⊆
      dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K))
    (hmax : dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K) ⊆
        dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K) →
      dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K) ⊆
        dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K)) : False := by
  set α₁ := connectedComponentIn (sphere c₁ r₁ \ K) y₁
  set α₂ := connectedComponentIn (sphere c₂ r₂ \ K) y₂
  obtain ⟨u₁, w₁, hB₁, -, -, -⟩ := p412d_arc hK hKc hKo hr₁ hy₁ hy₁K
  obtain ⟨u₂, w₂, -, hW₂, hα₂B, hα₂W⟩ := p412d_arc hK hKc hKo hr₂ hy₂ hy₂K
  have hy₂α : y₂ ∈ α₂ := mem_connectedComponentIn ⟨hy₂, hy₂K⟩
  have hα₂K : ∀ z ∈ α₂, z ∉ K := fun z hz => ((connectedComponentIn_subset _ _) hz).2
  have hT : IsPreconnected (dgW (α₂ ∪ K) ∪ α₂) := by
    have h := (isPreconnected_connectedComponentIn (F := (α₂ ∪ K)ᶜ) (x := w₂))
    rw [← hW₂] at h
    exact h.subset_closure subset_union_left (union_subset subset_closure hα₂W)
  have hTF : dgW (α₂ ∪ K) ∪ α₂ ⊆ (α₁ ∪ K)ᶜ := by
    rintro z (hz | hz) (h | h)
    · exact disjoint_left.1 (p412d_dgB_dgW_disj _) (hsub h) hz
    · exact hz.1 (Or.inr h)
    · exact hdis z h hz
    · exact hα₂K z hz h
  have hWne : (dgW (α₂ ∪ K)).Nonempty := closure_nonempty_iff.1 ⟨y₂, hα₂W hy₂α⟩
  have hTW : dgW (α₂ ∪ K) ∪ α₂ ⊆ dgW (α₁ ∪ K) := p412d_sub_dgW_of_unbdd hT hTF
    fun hb => p412d_dgW_unbdd hWne (hb.subset subset_union_left)
  have hB12 : dgB (α₁ ∪ K) ⊆ dgB (α₂ ∪ K) := by
    intro x hx
    have hxF : x ∉ α₂ ∪ K := by
      rintro (h | h)
      · exact disjoint_left.1 (p412d_dgB_dgW_disj _) hx (hTW (Or.inr h))
      · exact hx.1 (Or.inr h)
    rcases p412d_mem_dgB_or _ hxF with h | h
    · exact h
    · exact absurd (hTW (Or.inl h)) (disjoint_left.1 (p412d_dgB_dgW_disj _) hx)
  have hy₂B : y₂ ∈ closure (dgB (α₁ ∪ K)) := closure_mono (hmax hB12) (hα₂B hy₂α)
  rw [hB₁] at hy₂B
  rcases p412d_closure_cc (isClosed_cc_union K hK.isClosed c₁ y₁ r₁) u₁ hy₂B with h | h | h
  · rw [← hB₁] at h
    exact disjoint_left.1 (p412d_dgB_dgW_disj _) h (hTW (Or.inr hy₂α))
  · exact hdis y₂ h hy₂α
  · exact hy₂K h

/-- **Step 2** (DEC-86 (1); GM l. 2504–2518 with closures): two arcs with maximal bounded sides
whose closures both contain `y` have intersecting closures. -/
theorem p412d_max_meet {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c₁ c₂ y₁ y₂ y : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hy₁ : y₁ ∈ sphere c₁ r₁) (hy₁K : y₁ ∉ K) (hy₂ : y₂ ∈ sphere c₂ r₂) (hy₂K : y₂ ∉ K)
    (hcl : Disjoint (closure (connectedComponentIn (sphere c₁ r₁ \ K) y₁))
      (closure (connectedComponentIn (sphere c₂ r₂ \ K) y₂)))
    (hyS : y ∉ sphere c₁ r₁) (hLC : LocConnAt K y)
    (h₁ : y ∈ closure (dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K)))
    (h₂ : y ∈ closure (dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K)))
    (hmax₁ : dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K) ⊆
        dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K) →
      dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K) ⊆
        dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K))
    (hmax₂ : dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K) ⊆
        dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K) →
      dgB (connectedComponentIn (sphere c₁ r₁ \ K) y₁ ∪ K) ⊆
        dgB (connectedComponentIn (sphere c₂ r₂ \ K) y₂ ∪ K)) : False := by
  set α₁ := connectedComponentIn (sphere c₁ r₁ \ K) y₁
  set α₂ := connectedComponentIn (sphere c₂ r₂ \ K) y₂
  have hd₁₂ : ∀ x ∈ α₁, x ∉ α₂ := fun x h1 h2 =>
    disjoint_left.1 hcl (subset_closure h1) (subset_closure h2)
  have hd₂₁ : ∀ x ∈ α₂, x ∉ α₁ := fun x h2 h1 => hd₁₂ x h1 h2
  have hy₁α : y₁ ∈ α₁ := mem_connectedComponentIn ⟨hy₁, hy₁K⟩
  have hy₂α : y₂ ∈ α₂ := mem_connectedComponentIn ⟨hy₂, hy₂K⟩
  have hα₁F : α₁ ⊆ (α₂ ∪ K)ᶜ := by
    rintro z hz (h | h)
    · exact hd₁₂ z hz h
    · exact ((connectedComponentIn_subset _ _) hz).2 h
  have hα₂F : α₂ ⊆ (α₁ ∪ K)ᶜ := by
    rintro z hz (h | h)
    · exact hd₂₁ z hz h
    · exact ((connectedComponentIn_subset _ _) hz).2 h
  have hα₁W : α₁ ⊆ dgW (α₂ ∪ K) := by
    rcases p412d_mem_dgB_or _ (hα₁F hy₁α) with h | h
    · exact (p412d_max_aux hK hKc hKo hr₁ hr₂ hy₁ hy₁K hy₂ hy₂K hd₁₂
        (p412d_sub_dgB isPreconnected_connectedComponentIn hα₁F hy₁α h) hmax₁).elim
    · exact p412d_sub_dgW isPreconnected_connectedComponentIn hα₁F hy₁α h
  have hα₂W : α₂ ⊆ dgW (α₁ ∪ K) := by
    rcases p412d_mem_dgB_or _ (hα₂F hy₂α) with h | h
    · exact (p412d_max_aux hK hKc hKo hr₂ hr₁ hy₂ hy₂K hy₁ hy₁K hd₂₁
        (p412d_sub_dgB isPreconnected_connectedComponentIn hα₂F hy₂α h) hmax₂).elim
    · exact p412d_sub_dgW isPreconnected_connectedComponentIn hα₂F hy₂α h
  obtain ⟨u₂, w₂, hB₂, -, hα₂B, -⟩ := p412d_arc hK hKc hKo hr₂ hy₂ hy₂K
  have hP : IsPreconnected (dgB (α₂ ∪ K) ∪ α₂) := by
    have h := (isPreconnected_connectedComponentIn (F := (α₂ ∪ K)ᶜ) (x := u₂))
    rw [← hB₂] at h
    exact h.subset_closure subset_union_left (union_subset subset_closure hα₂B)
  have hPF : dgB (α₂ ∪ K) ∪ α₂ ⊆ (α₁ ∪ K)ᶜ := by
    rintro z (hz | hz) h
    · rcases h with h | h
      · exact disjoint_left.1 (p412d_dgB_dgW_disj _) hz (hα₁W h)
      · exact hz.1 (Or.inr h)
    · exact hα₂F hz h
  have hPW := p412d_sub_dgW hP hPF (Or.inr hy₂α) (hα₂W hy₂α)
  exact p412d_shadow_arc hK hKc hKo hr₁ hy₁ hy₁K hyS hLC h₁
    (closure_mono (fun z hz => hPW (Or.inl hz)) h₂)

end LQGMetric.GM
