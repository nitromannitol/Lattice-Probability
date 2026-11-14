/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RHit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDeg

 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC1R_safe_hits {S L R : Set ℂ}
    {α γ : ℝ → ℂ} {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) (hα : ContinuousOn α (Icc a₁ a₂))
    {c : ℂ} {r : ℝ} (hαA : ∀ v ∈ Icc a₁ a₂, r < dist (α v) c)
    (β : C(unitInterval, ℂ)) (hβ : β 0 = β 1)
    (hβS : ∀ t, β t ∈ S → ∃ v ∈ Icc a₁ a₂, β t = α v)
    (hin : ∀ q ∈ S, dist q c < r → ∃ h : ∀ t, β t ≠ q, laneC1RDeg β q h ≠ 0)
    (hR : ∀ q ∈ R, ∃ h : ∀ t, β t ≠ q, laneC1RDeg β q h = 0)
    (hL : ∀ q ∈ L, ∀ h : ∀ t, β t ≠ q, laneC1RDeg β q h ≠ 0 → α a₁ ∈ L ∨ α a₂ ∈ L)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) (hγS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S)
    (hγ0 : γ 0 ∈ L) (hγ1 : γ 1 ∈ R)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hvisit : dist (γ m) c < r) :
    ∃ v₀ ∈ Icc a₁ a₂, ∃ v₁ ∈ Icc a₁ a₂, ∃ t₀ t₁ : ℝ,
      t₀ ∈ Icc (0 : ℝ) 1 ∧ t₁ ∈ Icc (0 : ℝ) 1 ∧ t₀ ≤ t₁ ∧
      ((γ t₀ = α v₀ ∧ ∀ t ∈ Icc (0 : ℝ) t₀, r ≤ dist (γ t) c) ∨
        (t₀ = 0 ∧ α v₀ ∈ L)) ∧
      ((γ t₁ = α v₁ ∧ ∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c) ∨
        (t₁ = 1 ∧ α v₁ ∈ R)) := by
  have hK : IsCompact (α '' Icc a₁ a₂) := isCompact_Icc.image_of_continuousOn hα
  set T : Set ℝ := Icc (0 : ℝ) 1 ∩ γ ⁻¹' (α '' Icc a₁ a₂) with hTdef
  have hTc : IsClosed T := hγ.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed
  have hTsub : T ⊆ Icc (0 : ℝ) 1 := inter_subset_left
  have hTbdd : BddAbove T := ⟨1, fun t ht => (hTsub ht).2⟩
  have hTbddb : BddBelow T := ⟨0, fun t ht => (hTsub ht).1⟩
  
  have hTfar : ∀ t ∈ T, r < dist (γ t) c := by
    rintro t ⟨-, v, hv, hvt⟩
    rw [← hvt]
    exact hαA v hv
  
  have havoid : ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₂ ≤ 1 → (∀ t ∈ Icc s₁ s₂, t ∉ T) →
      ∀ t', ∀ s ∈ Icc s₁ s₂, β t' ≠ γ s := by
    intro s₁ s₂ h₁ h₂ hnot t' s hs heq
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨h₁.trans hs.1, hs.2.trans h₂⟩
    obtain ⟨v, hv, hβv⟩ := hβS t' (heq ▸ hγS s hs01)
    exact hnot s hs ⟨hs01, v, hv, (hβv.symm.trans heq)⟩
  
  have hsuffix : ∀ s ∈ Icc (0 : ℝ) 1, dist (γ s) c < r → ∃ t ∈ T, s ≤ t := by
    intro s hs hds
    by_contra hcon
    push Not at hcon
    have hnot : ∀ t ∈ Icc s 1, t ∉ T := fun t ht htT => (hcon t htT).not_ge ht.1
    have hav := havoid s 1 hs.1 le_rfl hnot
    have hpath := laneC1R_deg_eq_of_realPath hβ hs.2 (hγ.mono (Icc_subset_Icc hs.1 le_rfl)) hav
    obtain ⟨hsq, hdeg⟩ := hin (γ s) (hγS s hs) hds
    obtain ⟨h1, hdeg1⟩ := hR (γ 1) hγ1
    exact hdeg (hpath.trans hdeg1)
  
  have hprefix : (∀ h : ∀ t, β t ≠ γ 0, laneC1RDeg β (γ 0) h = 0) →
      ∀ s ∈ Icc (0 : ℝ) 1, dist (γ s) c < r → ∃ t ∈ T, t ≤ s := by
    intro hout s hs hds
    by_contra hcon
    push Not at hcon
    have hnot : ∀ t ∈ Icc 0 s, t ∉ T := fun t ht htT => (hcon t htT).not_ge ht.2
    have hav := havoid 0 s le_rfl hs.2 hnot
    have hpath := laneC1R_deg_eq_of_realPath hβ hs.1 (hγ.mono (Icc_subset_Icc le_rfl hs.2)) hav
    obtain ⟨hsq, hdeg⟩ := hin (γ s) (hγS s hs) hds
    exact hdeg (hpath.symm.trans (hout _))
  obtain ⟨tm, htmT, -⟩ := hsuffix m hm hvisit
  have hTne : T.Nonempty := ⟨tm, htmT⟩
  set t₁ : ℝ := sSup T with ht₁def
  have ht₁T : t₁ ∈ T := hTc.csSup_mem hTne hTbdd
  obtain ⟨v₁, hv₁, hv₁eq⟩ := ht₁T.2
  have hend : γ t₁ = α v₁ ∧ ∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c := by
    refine ⟨hv₁eq.symm, fun t ht => ?_⟩
    by_contra hlt
    push Not at hlt
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(hTsub ht₁T).1.trans ht.1, ht.2⟩
    obtain ⟨t', ht'T, htt'⟩ := hsuffix t ht01 hlt
    have ht'le : t' ≤ t₁ := le_csSup hTbdd ht'T
    have htT : t ∈ T := by
      have : t = t₁ := le_antisymm (htt'.trans ht'le) ht.1
      rw [this]
      exact ht₁T
    exact (hTfar t htT).not_gt hlt
  by_cases hLend : α a₁ ∈ L ∨ α a₂ ∈ L
  · have ht₁0 : 0 ≤ t₁ := (hTsub ht₁T).1
    rcases hLend with h | h
    · exact ⟨a₁, ⟨le_rfl, ha⟩, v₁, hv₁, 0, t₁, ⟨le_rfl, zero_le_one⟩, hTsub ht₁T, ht₁0,
        Or.inr ⟨rfl, h⟩, Or.inl hend⟩
    · exact ⟨a₂, ⟨ha, le_rfl⟩, v₁, hv₁, 0, t₁, ⟨le_rfl, zero_le_one⟩, hTsub ht₁T, ht₁0,
        Or.inr ⟨rfl, h⟩, Or.inl hend⟩
  · have hout : ∀ h : ∀ t, β t ≠ γ 0, laneC1RDeg β (γ 0) h = 0 := by
      intro h
      by_contra hne
      exact hLend (hL (γ 0) hγ0 h hne)
    set t₀ : ℝ := sInf T with ht₀def
    have ht₀T : t₀ ∈ T := hTc.csInf_mem hTne hTbddb
    obtain ⟨v₀, hv₀, hv₀eq⟩ := ht₀T.2
    have hstart : γ t₀ = α v₀ ∧ ∀ t ∈ Icc (0 : ℝ) t₀, r ≤ dist (γ t) c := by
      refine ⟨hv₀eq.symm, fun t ht => ?_⟩
      by_contra hlt
      push Not at hlt
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (hTsub ht₀T).2⟩
      obtain ⟨t', ht'T, ht't⟩ := hprefix hout t ht01 hlt
      have ht'ge : t₀ ≤ t' := csInf_le hTbddb ht'T
      have htT : t ∈ T := by
        have : t = t₀ := le_antisymm ht.2 (ht'ge.trans ht't)
        rw [this]
        exact ht₀T
      exact (hTfar t htT).not_gt hlt
    exact ⟨v₀, hv₀, v₁, hv₁, t₀, t₁, hTsub ht₀T, hTsub ht₁T,
      csInf_le_csSup hTne hTbddb hTbdd, Or.inl hstart, Or.inl hend⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
