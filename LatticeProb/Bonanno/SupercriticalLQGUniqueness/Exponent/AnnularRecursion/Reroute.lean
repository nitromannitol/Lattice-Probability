/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Reroute at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.ReImTopology




 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

 
def rectC (c₁ c₂ d₁ d₂ : ℝ) : Set ℂ := Icc c₁ c₂ ×ℂ Icc d₁ d₂

 
def rectO (c₁ c₂ d₁ d₂ : ℝ) : Set ℂ := Ioo c₁ c₂ ×ℂ Ioo d₁ d₂

 
def rectSides (c₁ c₂ d₁ d₂ : ℝ) : Set ℂ :=
  ((Icc c₁ c₂ ×ℂ {d₁}) ∪ ({c₁} ×ℂ Icc d₁ d₂)) ∪ (Icc c₁ c₂ ×ℂ {d₂}) ∪
    ({c₂} ×ℂ Icc d₁ d₂)

theorem convex_reProdIm' {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ (s ×ℂ t) :=
  (hs.linear_preimage Complex.reLm).inter (ht.linear_preimage Complex.imLm)

theorem isClosed_rectC (c₁ c₂ d₁ d₂ : ℝ) : IsClosed (rectC c₁ c₂ d₁ d₂) :=
  isClosed_Icc.reProdIm isClosed_Icc

theorem isOpen_rectO (c₁ c₂ d₁ d₂ : ℝ) : IsOpen (rectO c₁ c₂ d₁ d₂) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem rectO_subset_rectC (c₁ c₂ d₁ d₂ : ℝ) : rectO c₁ c₂ d₁ d₂ ⊆ rectC c₁ c₂ d₁ d₂ := by
  rintro z ⟨h1, h2⟩
  exact ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩

theorem rectSides_subset_rectC {c₁ c₂ d₁ d₂ : ℝ} (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂) :
    rectSides c₁ c₂ d₁ d₂ ⊆ rectC c₁ c₂ d₁ d₂ := by
  rintro z (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
  · have e : z.im = d₁ := h2
    refine ⟨h1, ?_⟩
    show z.im ∈ Icc d₁ d₂
    rw [e]; exact ⟨le_rfl, hd⟩
  · have e : z.re = c₁ := h1
    refine ⟨?_, h2⟩
    show z.re ∈ Icc c₁ c₂
    rw [e]; exact ⟨le_rfl, hc⟩
  · have e : z.im = d₂ := h2
    refine ⟨h1, ?_⟩
    show z.im ∈ Icc d₁ d₂
    rw [e]; exact ⟨hd, le_rfl⟩
  · have e : z.re = c₂ := h1
    refine ⟨?_, h2⟩
    show z.re ∈ Icc c₁ c₂
    rw [e]; exact ⟨hc, le_rfl⟩

theorem mem_rectSides_of_not_rectO {c₁ c₂ d₁ d₂ : ℝ} {z : ℂ}
    (h1 : z ∈ rectC c₁ c₂ d₁ d₂) (h2 : z ∉ rectO c₁ c₂ d₁ d₂) :
    z ∈ rectSides c₁ c₂ d₁ d₂ := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := h1
  simp only [rectO, Complex.mem_reProdIm, mem_Ioo, not_and_or, not_lt] at h2
  simp only [rectSides, mem_union, Complex.mem_reProdIm, mem_Icc, mem_singleton_iff]
  rcases h2 with (h | h) | (h | h)
  · left; left; right; exact ⟨le_antisymm h a1, b1, b2⟩
  · right; exact ⟨le_antisymm a2 h, b1, b2⟩
  · left; left; left; exact ⟨⟨a1, a2⟩, le_antisymm h b1⟩
  · left; right; exact ⟨⟨a1, a2⟩, le_antisymm b2 h⟩

theorem isPathConnected_rectSides {c₁ c₂ d₁ d₂ : ℝ} (hc : c₁ ≤ c₂) (hd : d₁ ≤ d₂) :
    IsPathConnected (rectSides c₁ c₂ d₁ d₂) := by
  have hB : IsPathConnected (Icc c₁ c₂ ×ℂ {d₁}) :=
    (convex_reProdIm' (convex_Icc _ _) (convex_singleton _)).isPathConnected
      ⟨⟨c₁, d₁⟩, ⟨⟨le_rfl, hc⟩, rfl⟩⟩
  have hL : IsPathConnected ({c₁} ×ℂ Icc d₁ d₂) :=
    (convex_reProdIm' (convex_singleton _) (convex_Icc _ _)).isPathConnected
      ⟨⟨c₁, d₁⟩, ⟨rfl, ⟨le_rfl, hd⟩⟩⟩
  have hT : IsPathConnected (Icc c₁ c₂ ×ℂ {d₂}) :=
    (convex_reProdIm' (convex_Icc _ _) (convex_singleton _)).isPathConnected
      ⟨⟨c₁, d₂⟩, ⟨⟨le_rfl, hc⟩, rfl⟩⟩
  have hR : IsPathConnected ({c₂} ×ℂ Icc d₁ d₂) :=
    (convex_reProdIm' (convex_singleton _) (convex_Icc _ _)).isPathConnected
      ⟨⟨c₂, d₁⟩, ⟨rfl, ⟨le_rfl, hd⟩⟩⟩
  refine ((hB.union hL ?_).union hT ?_).union hR ?_
  · exact ⟨⟨c₁, d₁⟩, ⟨⟨le_rfl, hc⟩, rfl⟩, ⟨rfl, ⟨le_rfl, hd⟩⟩⟩
  · exact ⟨⟨c₁, d₂⟩, Or.inr ⟨rfl, ⟨hd, le_rfl⟩⟩, ⟨⟨le_rfl, hc⟩, rfl⟩⟩
  · exact ⟨⟨c₂, d₁⟩, Or.inl (Or.inl ⟨⟨hc, le_rfl⟩, rfl⟩), ⟨rfl, ⟨le_rfl, hd⟩⟩⟩

 
theorem reroute_rect {x y : ℂ} (γ : Path x y) {c₁ c₂ d₁ d₂ : ℝ} (hc : c₁ ≤ c₂)
    (hd : d₁ ≤ d₂) (hx : x ∉ rectC c₁ c₂ d₁ d₂) (hy : y ∉ rectC c₁ c₂ d₁ d₂) :
    JoinedIn ((range γ \ rectC c₁ c₂ d₁ d₂) ∪ rectSides c₁ c₂ d₁ d₂) x y := by
  set R := rectC c₁ c₂ d₁ d₂ with hR
  set S := (range γ \ R) ∪ rectSides c₁ c₂ d₁ d₂ with hS
  set g : ℝ → ℂ := ⇑γ.extend with hg
  have hgc : Continuous g := γ.extend.continuous
  have hg0 : g 0 = x := γ.extend_zero
  have hg1 : g 1 = y := γ.extend_one
  have hgr : ∀ t, g t ∈ range γ := fun t => by
    rw [← γ.extend_range]; exact mem_range_self t
  by_cases hmeet : ∃ t ∈ Icc (0 : ℝ) 1, g t ∈ R
  · set T : Set ℝ := Icc (0 : ℝ) 1 ∩ g ⁻¹' R with hT
    have hTc : IsClosed T := isClosed_Icc.inter ((isClosed_rectC _ _ _ _).preimage hgc)
    have hTne : T.Nonempty := by
      obtain ⟨t, ht, hgt⟩ := hmeet; exact ⟨t, ht, hgt⟩
    have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
    have hTa : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
    set t₁ := sInf T
    set t₂ := sSup T
    have ht₁ : t₁ ∈ T := hTc.csInf_mem hTne hTb
    have ht₂ : t₂ ∈ T := hTc.csSup_mem hTne hTa
    have h12 : t₁ ≤ t₂ := csInf_le_csSup hTne hTb hTa
    have hbefore : ∀ t ∈ Icc (0 : ℝ) 1, t < t₁ → g t ∉ R := fun t ht hlt hgt =>
      absurd (csInf_le hTb ⟨ht, hgt⟩) (not_le.2 hlt)
    have hafter : ∀ t ∈ Icc (0 : ℝ) 1, t₂ < t → g t ∉ R := fun t ht hlt hgt =>
      absurd (le_csSup hTa ⟨ht, hgt⟩) (not_le.2 hlt)
    have ht₁pos : 0 < t₁ := by
      rcases ht₁.1.1.lt_or_eq with h | h
      · exact h
      · exfalso; apply hx; rw [← hg0, h]; exact ht₁.2
    have ht₂lt : t₂ < 1 := by
      rcases ht₂.1.2.lt_or_eq with h | h
      · exact h
      · exfalso; apply hy; rw [← hg1, ← h]; exact ht₂.2
    
    have hside₁ : g t₁ ∈ rectSides c₁ c₂ d₁ d₂ := by
      refine mem_rectSides_of_not_rectO ht₁.2 fun hO => ?_
      have hU : g ⁻¹' rectO c₁ c₂ d₁ d₂ ∈ nhds t₁ :=
        hgc.continuousAt.preimage_mem_nhds ((isOpen_rectO _ _ _ _).mem_nhds hO)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = t₁ - min ε t₁ / 2 := ⟨_, rfl⟩
      have hm : 0 < min ε t₁ := lt_min hε ht₁pos
      have hmt : min ε t₁ ≤ t₁ := min_le_right _ _
      have hme : min ε t₁ ≤ ε := min_le_left _ _
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht₁.1.2]⟩
      have htd : t ∈ Metric.ball t₁ ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
      exact hbefore t htI (by linarith) (rectO_subset_rectC _ _ _ _ (hball htd))
    have hside₂ : g t₂ ∈ rectSides c₁ c₂ d₁ d₂ := by
      refine mem_rectSides_of_not_rectO ht₂.2 fun hO => ?_
      have hU : g ⁻¹' rectO c₁ c₂ d₁ d₂ ∈ nhds t₂ :=
        hgc.continuousAt.preimage_mem_nhds ((isOpen_rectO _ _ _ _).mem_nhds hO)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = t₂ + min ε (1 - t₂) / 2 := ⟨_, rfl⟩
      have hm : 0 < min ε (1 - t₂) := lt_min hε (by linarith)
      have hmt : min ε (1 - t₂) ≤ 1 - t₂ := min_le_right _ _
      have hme : min ε (1 - t₂) ≤ ε := min_le_left _ _
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht₂.1.1], by linarith⟩
      have htd : t ∈ Metric.ball t₂ ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
      exact hafter t htI (by linarith) (rectO_subset_rectC _ _ _ _ (hball htd))
    
    have hP₁ : IsPathConnected (g '' Icc 0 t₁) :=
      ((convex_Icc 0 t₁).isPathConnected (nonempty_Icc.2 ht₁pos.le)).image hgc
    have hP₂ : IsPathConnected (g '' Icc t₂ 1) :=
      ((convex_Icc t₂ 1).isPathConnected (nonempty_Icc.2 ht₂lt.le)).image hgc
    have hj₁ : JoinedIn (g '' Icc 0 t₁) x (g t₁) := by
      rw [← hg0]
      exact hP₁.joinedIn _ (mem_image_of_mem g ⟨le_rfl, ht₁pos.le⟩) _
        (mem_image_of_mem g ⟨ht₁pos.le, le_rfl⟩)
    have hj₂ : JoinedIn (rectSides c₁ c₂ d₁ d₂) (g t₁) (g t₂) :=
      (isPathConnected_rectSides hc hd).joinedIn _ hside₁ _ hside₂
    have hj₃ : JoinedIn (g '' Icc t₂ 1) (g t₂) y := by
      rw [← hg1]
      exact hP₂.joinedIn _ (mem_image_of_mem g ⟨le_rfl, ht₂lt.le⟩) _
        (mem_image_of_mem g ⟨ht₂lt.le, le_rfl⟩)
    have hs₁ : g '' Icc 0 t₁ ⊆ S := by
      rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
      rcases h1.lt_or_eq with h | h
      · exact Or.inl ⟨hgr t, hbefore t ⟨h0, by linarith [ht₁.1.2]⟩ h⟩
      · rw [h]; exact Or.inr hside₁
    have hs₃ : g '' Icc t₂ 1 ⊆ S := by
      rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
      rcases h0.lt_or_eq with h | h
      · exact Or.inl ⟨hgr t, hafter t ⟨by linarith [ht₂.1.1], h1⟩ h⟩
      · rw [← h]; exact Or.inr hside₂
    exact (hj₁.mono hs₁).trans ((hj₂.mono subset_union_right).trans (hj₃.mono hs₃))
  · refine ⟨γ, fun t => Or.inl ⟨mem_range_self t, fun hgt => hmeet ⟨t.1, t.2, ?_⟩⟩⟩
    rw [hg, Path.extend_extends']
    exact hgt

 
theorem reroute_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c₁ c₂ d₁ d₂ : ι → ℝ) (hc : ∀ i ∈ s, c₁ i ≤ c₂ i) (hd : ∀ i ∈ s, d₁ i ≤ d₂ i)
    {x y : ℂ} (γ : Path x y) (hx : ∀ i ∈ s, x ∉ rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i))
    (hy : ∀ i ∈ s, y ∉ rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i)) :
    JoinedIn ((range γ \ ⋃ i ∈ s, rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i)) ∪
      ⋃ i ∈ s, rectSides (c₁ i) (c₂ i) (d₁ i) (d₂ i)) x y := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨γ, fun t => Or.inl ⟨mem_range_self t, ?_⟩⟩
    simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
      (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    set γ' := ih'.somePath
    have hγ' : ∀ t, γ' t ∈ (range γ \ ⋃ i ∈ s, rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i)) ∪
        ⋃ i ∈ s, rectSides (c₁ i) (c₂ i) (d₁ i) (d₂ i) := ih'.somePath_mem
    have hstep := reroute_rect γ' (hc a (Finset.mem_insert_self a s))
      (hd a (Finset.mem_insert_self a s)) (hx a (Finset.mem_insert_self a s))
      (hy a (Finset.mem_insert_self a s))
    refine hstep.mono ?_
    rintro z (⟨⟨t, rfl⟩, hza⟩ | hz)
    · rcases hγ' t with ⟨hzγ, hzs⟩ | hzs
      · left
        refine ⟨hzγ, ?_⟩
        simp only [Finset.mem_insert, mem_iUnion, exists_prop, not_exists, not_and]
        rintro i (rfl | hi)
        · exact hza
        · intro h; exact hzs (mem_iUnion₂.2 ⟨i, hi, h⟩)
      · right
        obtain ⟨i, hi, h⟩ := mem_iUnion₂.1 hzs
        exact mem_iUnion₂.2 ⟨i, Finset.mem_insert_of_mem hi, h⟩
    · right
      exact mem_iUnion₂.2 ⟨a, Finset.mem_insert_self a s, hz⟩

 


theorem disconnects_of_short_loops {K I J : Set ℂ} (hK : LQGMetric.Disconnects K I J)
    {ι : Type*} [DecidableEq ι] (tiles long : Finset ι) (T : ι → Set ℂ)
    (hcover : K ⊆ ⋃ i ∈ tiles, T i) (c₁ c₂ d₁ d₂ : ι → ℝ)
    (hshort : ∀ i ∈ tiles, i ∉ long → (T i ∩ K).Nonempty →
      c₁ i ≤ c₂ i ∧ d₁ i ≤ d₂ i ∧ T i ⊆ rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i) ∧
        Disjoint (rectSides (c₁ i) (c₂ i) (d₁ i) (d₂ i)) K ∧
        Disjoint (rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i)) I ∧
        Disjoint (rectC (c₁ i) (c₂ i) (d₁ i) (d₂ i)) J) :
    LQGMetric.Disconnects (⋃ i ∈ long, T i) I J := by
  classical
  intro x y γ hx hy
  by_contra hno
  rw [not_nonempty_iff_eq_empty] at hno
  set Sh := tiles.filter (fun i => i ∉ long ∧ (T i ∩ K).Nonempty) with hSh
  have hmemSh : ∀ i ∈ Sh, i ∈ tiles ∧ i ∉ long ∧ (T i ∩ K).Nonempty := fun i hi => by
    rw [hSh, Finset.mem_filter] at hi; exact ⟨hi.1, hi.2.1, hi.2.2⟩
  have hdata := fun i (hi : i ∈ Sh) =>
    hshort i (hmemSh i hi).1 (hmemSh i hi).2.1 (hmemSh i hi).2.2
  have hj := reroute_finset Sh c₁ c₂ d₁ d₂ (fun i hi => (hdata i hi).1)
    (fun i hi => (hdata i hi).2.1) γ
    (fun i hi hxi => (hdata i hi).2.2.2.2.1.le_bot ⟨hxi, hx⟩)
    (fun i hi hyi => (hdata i hi).2.2.2.2.2.le_bot ⟨hyi, hy⟩)
  obtain ⟨w, ⟨t, rfl⟩, hwK⟩ := hK x y hj.somePath hx hy
  rcases hj.somePath_mem t with ⟨hwγ, hwR⟩ | hwS
  · obtain ⟨i, hi, hwT⟩ := mem_iUnion₂.1 (hcover hwK)
    by_cases hil : i ∈ long
    · have : hj.somePath t ∈ range γ ∩ ⋃ i ∈ long, T i := ⟨hwγ, mem_iUnion₂.2 ⟨i, hil, hwT⟩⟩
      rw [hno] at this
      exact this
    · have hiSh : i ∈ Sh := by
        rw [hSh, Finset.mem_filter]; exact ⟨hi, hil, ⟨_, hwT, hwK⟩⟩
      exact hwR (mem_iUnion₂.2 ⟨i, hiSh, (hdata i hiSh).2.2.1 hwT⟩)
  · obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.1 hwS
    exact (hdata i hi).2.2.2.1.le_bot ⟨hwi, hwK⟩



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
