/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RSepData at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RClose
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDip
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLift

 


















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex Metric QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

theorem laneC1R_re_lt_of_annulus {z c : ℂ} {r : ℝ} (hz : dist z c < 2 * r)
    (hcR : c.re + 2 * r ≤ 1) : z.re < 1 := by
  have h := Complex.abs_re_le_norm (z - c)
  rw [← dist_eq_norm] at h
  have : z.re - c.re ≤ |(z - c).re| := by simpa using le_abs_self (z - c).re
  linarith

theorem laneC1R_im_pos_of_annulus {z c : ℂ} {r : ℝ} (hz : dist z c < 2 * r)
    (hcB : 2 * r ≤ c.im) : 0 < z.im := by
  have h := Complex.abs_im_le_norm (z - c)
  rw [← dist_eq_norm] at h
  have : c.im - z.im ≤ |(z - c).im| := by
    have := neg_abs_le (z - c).im
    simp at this ⊢
    linarith
  linarith

 
theorem laneC1R_seg_mem_square_ball {p q c : ℂ} {r : ℝ}
    (hp : p ∈ (rectAB 1 1).toSet) (hq : q ∈ (rectAB 1 1).toSet)
    (hpc : dist p c < r) (hqc : dist q c < r) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    p + (s : ℂ) * (q - p) ∈ (rectAB 1 1).toSet ∧ dist (p + (s : ℂ) * (q - p)) c < r := by
  rw [mem_rectAB_toSet] at hp hq ⊢
  obtain ⟨hs0, hs1⟩ := hs
  have hre : (p + (s : ℂ) * (q - p)).re = (1 - s) * p.re + s * q.re := by simp; ring
  have him : (p + (s : ℂ) * (q - p)).im = (1 - s) * p.im + s * q.im := by simp; ring
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hre]; nlinarith [hp.1.1, hq.1.1]
  · rw [hre]; nlinarith [hp.1.2, hq.1.2]
  · rw [him]; nlinarith [hp.2.1, hq.2.1]
  · rw [him]; nlinarith [hp.2.2, hq.2.2]
  · have e : p + (s : ℂ) * (q - p) - c = ((1 - s : ℝ) : ℂ) * (p - c) + (s : ℂ) * (q - c) := by
      push_cast; ring
    rw [dist_eq_norm, e]
    calc ‖((1 - s : ℝ) : ℂ) * (p - c) + (s : ℂ) * (q - c)‖
        ≤ ‖((1 - s : ℝ) : ℂ) * (p - c)‖ + ‖(s : ℂ) * (q - c)‖ := norm_add_le _ _
      _ = (1 - s) * dist p c + s * dist q c := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hs0, dist_eq_norm,
            dist_eq_norm]
      _ < r := by
          rcases eq_or_lt_of_le hs0 with h | h
          · rw [← h]; simp; exact hpc
          · nlinarith

 
theorem laneC1R_hin_of_point {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1) {c p : ℂ} {r : ℝ}
    (hpS : p ∈ (rectAB 1 1).toSet) (hpc : dist p c < r)
    (havoid : ∀ t, β t ∈ (rectAB 1 1).toSet → r < dist (β t) c)
    (hp : ∃ h : ∀ t, β t ≠ p, laneC1RDeg β p h ≠ 0) :
    ∀ q ∈ (rectAB 1 1).toSet, dist q c < r → ∃ h : ∀ t, β t ≠ q, laneC1RDeg β q h ≠ 0 := by
  intro q hqS hqc
  obtain ⟨hpne, hdeg⟩ := hp
  have hav : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1, β t ≠ p + (s : ℂ) * (q - p) := by
    intro t s hs heq
    obtain ⟨hS, hd⟩ := laneC1R_seg_mem_square_ball hpS hqS hpc hqc hs
    have := havoid t (heq ▸ hS)
    rw [heq] at this
    linarith
  have hqne : ∀ t, β t ≠ q := by
    intro t
    have := hav t 1 ⟨zero_le_one, le_rfl⟩
    simpa using this
  exact ⟨hqne, by rw [← laneC1R_deg_eq_of_segment hβ hav hpne hqne]; exact hdeg⟩

 
theorem laneC1R_right_deg_zero {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1)
    (hre : ∀ t, (β t).re < 1) :
    ∀ q ∈ (rectAB 1 1).side₂, ∃ h : ∀ t, β t ≠ q, laneC1RDeg β q h = 0 := by
  intro q hq
  have hq1 : q.re = 1 := (mem_rectAB_side₂.mp hq).1
  have hray : ∀ t, ∀ s : ℝ, 0 ≤ s → β t ≠ q + (s : ℂ) * 1 := by
    intro t s hs heq
    have := congrArg Complex.re heq
    simp at this
    linarith [hre t]
  have hne : ∀ t, β t ≠ q := fun t => by simpa using hray t 0 le_rfl
  exact ⟨hne, laneC1R_deg_eq_zero_of_ray hβ one_ne_zero hray hne⟩

 
theorem laneC1R_left_deg_zero {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1)
    (hpos : ∀ t, 0 < (β t).re ∨ 1 < (β t).im) :
    ∀ q ∈ (rectAB 1 1).side₁, ∀ h : ∀ t, β t ≠ q, laneC1RDeg β q h = 0 := by
  intro q hq h
  have hq0 : q.re = 0 := (mem_rectAB_side₁.mp hq).1
  have hq1 : q.im ≤ 1 := (mem_rectAB_side₁.mp hq).2.2
  have hray : ∀ t, ∀ s : ℝ, 0 ≤ s → β t ≠ q + (s : ℂ) * (-1) := by
    intro t s hs heq
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    simp at hr hi
    rcases hpos t with h1 | h1 <;> linarith
  exact laneC1R_deg_eq_zero_of_ray hβ (by norm_num) hray h

 
theorem laneC1R_quadrant_sepdata {τ : ℝ → ℂ} (hτ : ContinuousOn τ (Icc (0 : ℝ) 1))
    (hclosed : τ 0 = τ 1) {c p : ℂ} {r : ℝ}
    (hτann : ∀ u ∈ Icc (0 : ℝ) 1, r < dist (τ u) c ∧ dist (τ u) c < 2 * r)
    (hcR : c.re + 2 * r ≤ 1) (hcB : 2 * r ≤ c.im)
    (hp0 : 0 < p.re) (hp1 : p.im < 1) (hpS : p ∈ (rectAB 1 1).toSet) (hpc : dist p c < r)
    {M : ℝ → ℂ} (hM : ContinuousOn M (Icc (0 : ℝ) 1))
    (hMexp : ∀ u ∈ Icc (0 : ℝ) 1, Complex.exp (M u) = τ u - p)
    (hMjump : M 1 - M 0 ≠ 0) :
    ∃ (σ : ℝ → ℂ) (a₁ a₂ : ℝ) (β : C(unitInterval, ℂ)),
      0 ≤ a₁ ∧ a₁ ≤ a₂ ∧ a₂ ≤ 1 ∧ ContinuousOn σ (Icc (0 : ℝ) 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1, r < dist (σ v) c ∧ dist (σ v) c < 2 * r) ∧
      (∀ D : ContMetric, D.len σ 0 1 ≤ D.len τ 0 1) ∧
      (∀ v ∈ Icc a₁ a₂, σ v ∈ (rectAB 1 1).toSet) ∧
      β 0 = β 1 ∧
      (∀ t, β t ∈ (rectAB 1 1).toSet → ∃ v ∈ Icc a₁ a₂, β t = σ v) ∧
      (∀ q ∈ (rectAB 1 1).toSet, dist q c < r →
        ∃ h : ∀ t, β t ≠ q, laneC1RDeg β q h ≠ 0) ∧
      (∀ q ∈ (rectAB 1 1).side₂, ∃ h : ∀ t, β t ≠ q, laneC1RDeg β q h = 0) ∧
      (∀ q ∈ (rectAB 1 1).side₁, ∀ h : ∀ t, β t ≠ q, laneC1RDeg β q h ≠ 0 →
        σ a₁ ∈ (rectAB 1 1).side₁ ∨ σ a₂ ∈ (rectAB 1 1).side₁) := by
  have hσsq_of : ∀ z : ℂ, dist z c < 2 * r → 0 ≤ z.re → z.im ≤ 1 →
      z ∈ (rectAB 1 1).toSet := by
    intro z hz h0 h1
    rw [mem_rectAB_toSet]
    exact ⟨⟨h0, (laneC1R_re_lt_of_annulus hz hcR).le⟩,
      ⟨(laneC1R_im_pos_of_annulus hz hcB).le, h1⟩⟩
  by_cases hF : ∃ u₀ ∈ Icc (0 : ℝ) 1, τ u₀ ∈ laneC1RQc
  · 
    obtain ⟨u₀, hu₀, hu₀Q⟩ := hF
    have hu₀2 : u₀ ∈ Icc (0 : ℝ) 2 := ⟨hu₀.1, by linarith [hu₀.2]⟩
    have hu₀12 : u₀ + 1 ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hu₀.1], by linarith [hu₀.2]⟩
    let σ := SupercriticalLQGUniqueness.B2.Strong.seg (laneCRepeatLoop τ) u₀ (u₀ + 1)
    let Λσ := SupercriticalLQGUniqueness.B2.Strong.seg (laneCRepeatLift M) u₀ (u₀ + 1)
    have hσc : ContinuousOn σ (Icc (0 : ℝ) 1) :=
      SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg
        (laneC_repeatLoop_continuousOn hτ hclosed) hu₀2 hu₀12
    have hΛc : ContinuousOn Λσ (Icc (0 : ℝ) 1) :=
      SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg
        (laneC_repeatLift_continuousOn hM) hu₀2 hu₀12
    have hpar : ∀ s ∈ Icc (0 : ℝ) 1, u₀ + s * (u₀ + 1 - u₀) ∈ Icc (0 : ℝ) 2 :=
      fun s hs => SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hu₀2 hu₀12 hs
    have hσann : ∀ v ∈ Icc (0 : ℝ) 1, r < dist (σ v) c ∧ dist (σ v) c < 2 * r := by
      intro v hv
      exact laneC_repeatLoop_mapsTo (A := {z | r < dist z c ∧ dist z c < 2 * r}) hclosed
        hτann _ (hpar v hv)
    have hΛexp : ∀ s ∈ Icc (0 : ℝ) 1, Complex.exp (Λσ s) = σ s - p := fun s hs =>
      laneC_repeatLift_exp hclosed hMexp _ (hpar s hs)
    have hσ0 : σ 0 = τ u₀ := by
      simp only [σ, SupercriticalLQGUniqueness.B2.Strong.seg_zero]
      exact laneC_repeatLoop_first τ hu₀
    have hσ1 : σ 1 = σ 0 := by
      rw [hσ0]
      simp only [σ, SupercriticalLQGUniqueness.B2.Strong.seg_one]
      exact laneC_repeatLoop_shift hclosed hu₀
    have hΛjump : Λσ 1 - Λσ 0 ≠ 0 := by
      simp only [Λσ, SupercriticalLQGUniqueness.B2.Strong.seg_zero,
        SupercriticalLQGUniqueness.B2.Strong.seg_one]
      rw [laneC_repeatLift_shift M hu₀, laneC_repeatLift_first M hu₀]
      simpa using hMjump
    have hσp : ∀ s ∈ Icc (0 : ℝ) 1, σ s ≠ p := by
      intro s hs heq
      have := (hσann s hs).1
      rw [heq] at this
      linarith
    obtain ⟨l, u, hl0, hlu, hu1, hlQ, huQ, hgap, hjump⟩ :=
      laneC1R_exists_jump_gap laneC1RQc_closed hσc hΛc hΛexp
        (laneC1R_branch_continuousOn hp0 hp1) (fun z hz => laneC1R_branch_exp hp0 hp1 hz)
        hσp (by rw [hσ0]; exact hu₀Q) hσ1 hΛjump
    have hIcc : Icc l u ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hl0 hu1
    
    have hclosQ : ∀ s ∈ Icc l u, 0 ≤ (σ s).re ∧ (σ s).im ≤ 1 := by
      have hC : IsClosed {z : ℂ | 0 ≤ z.re ∧ z.im ≤ 1} :=
        (isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_im continuous_const)
      have hsub : σ '' Ioo l u ⊆ {z : ℂ | 0 ≤ z.re ∧ z.im ≤ 1} := by
        rintro _ ⟨s, hs, rfl⟩
        have h := hgap s hs
        simp only [laneC1RQc, mem_setOf_eq, not_or, not_le] at h
        exact ⟨h.1.le, h.2.le⟩
      intro s hs
      have hcl : closure (Ioo l u) = Icc l u := closure_Ioo hlu.ne
      have himg := ContinuousOn.image_closure (s := Ioo l u) (by rw [hcl]; exact hσc.mono hIcc)
      have : σ s ∈ closure (σ '' Ioo l u) := himg ⟨s, by rw [hcl]; exact hs, rfl⟩
      exact closure_minimal hsub hC this
    have hσS : ∀ s ∈ Icc l u, σ s ∈ (rectAB 1 1).toSet := fun s hs =>
      hσsq_of _ (hσann s (hIcc hs)).2 (hclosQ s hs).1 (hclosQ s hs).2
    have hbdry : ∀ s ∈ Icc l u, σ s ∈ laneC1RQc → laneC1RBdry (σ s) := by
      intro s hs hQ
      obtain ⟨h0, h1⟩ := hclosQ s hs
      have hann := (hσann s (hIcc hs)).2
      refine ⟨h0, laneC1R_re_lt_of_annulus hann hcR, laneC1R_im_pos_of_annulus hann hcB, h1, ?_⟩
      rcases hQ with h | h
      · exact Or.inl (le_antisymm h h0)
      · exact Or.inr (le_antisymm h1 h)
    have hlmem : l ∈ Icc l u := ⟨le_rfl, hlu.le⟩
    have humem : u ∈ Icc l u := ⟨hlu.le, le_rfl⟩
    have hBl : laneC1RBdry (σ l) := hbdry l hlmem hlQ
    have hBu : laneC1RBdry (σ u) := hbdry u humem huQ
    let ext := laneC1RExt (σ u) (σ l)
    have hσlu : ContinuousOn σ (Icc l u) := hσc.mono hIcc
    let β : C(unitInterval, ℂ) := (laneC1RArcPath σ l u hlu.le hσlu).trans ext
    have hextgood : ∀ t, laneC1RExtGood (σ u) (σ l) (ext t) := laneC1RExt_good hBu hBl
    obtain ⟨hpne, hpdeg⟩ := laneC1R_closed_jump_deg hlu.le hσlu (hΛc.mono hIcc)
      (fun s hs => hΛexp s (hIcc hs)) ext (laneC1R_branch_continuousOn hp0 hp1)
      (fun z hz => laneC1R_branch_exp hp0 hp1 hz) (fun t => (hextgood t).1) hjump
    have hβ01 : β 0 = β 1 := by
      change ((laneC1RArcPath σ l u hlu.le hσlu).trans ext) 0 =
        ((laneC1RArcPath σ l u hlu.le hσlu).trans ext) 1
      rw [Path.source, Path.target]
    
    have hβpt : ∀ t, (∃ s ∈ Icc l u, β t = σ s) ∨ laneC1RExtGood (σ u) (σ l) (β t) := by
      intro t
      have hmem : β t ∈ range ((laneC1RArcPath σ l u hlu.le hσlu).trans ext) := ⟨t, rfl⟩
      rw [Path.trans_range] at hmem
      rcases hmem with h | h
      · exact Or.inl (laneC1RArcPath_range h)
      · obtain ⟨t', ht'⟩ := h
        right
        rw [← ht']
        exact hextgood t'
    have hβS : ∀ t, β t ∈ (rectAB 1 1).toSet → ∃ v ∈ Icc l u, β t = σ v := by
      intro t hS
      rcases hβpt t with h | h
      · exact h
      · have hS' := mem_rectAB_toSet.mp hS
        rcases h.2.1 ⟨hS'.1.1, hS'.1.2, hS'.2.1, hS'.2.2⟩ with h' | h'
        · exact ⟨u, humem, h'⟩
        · exact ⟨l, hlmem, h'⟩
    refine ⟨σ, l, u, β, hl0, hlu.le, hu1, hσc, hσann, ?_, hσS, hβ01, hβS, ?_, ?_, ?_⟩
    · intro D
      exact laneC_repeatLoop_segment_cost_any D hclosed hu₀2 (by linarith) hu₀12.2 le_rfl
    · refine laneC1R_hin_of_point hβ01 hpS hpc (fun t hS => ?_) ⟨hpne, hpdeg⟩
      obtain ⟨v, hv, hβv⟩ := hβS t hS
      rw [hβv]
      exact (hσann v (hIcc hv)).1
    · apply laneC1R_right_deg_zero hβ01
      intro t
      rcases hβpt t with ⟨s, hs, h⟩ | h
      · rw [h]; exact laneC1R_re_lt_of_annulus (hσann s (hIcc hs)).2 hcR
      · exact h.2.2.1
    · intro q hq h hdeg
      by_contra hnot
      push Not at hnot
      have hre_ne : ∀ s ∈ Icc l u, σ s ∉ (rectAB 1 1).side₁ → (σ s).re ≠ 0 := by
        intro s hs hns h0
        apply hns
        have hS' := mem_rectAB_toSet.mp (hσS s hs)
        exact mem_rectAB_side₁.mpr ⟨h0, hS'.2⟩
      have hl_ne := hre_ne l hlmem hnot.1
      have hu_ne := hre_ne u humem hnot.2
      have hpos : ∀ t, 0 < (β t).re ∨ 1 < (β t).im := by
        intro t
        rcases hβpt t with ⟨s, hs, hst⟩ | h
        · left
          rw [hst]
          rcases eq_or_lt_of_le hs.1 with hsl | hsl
          · rw [← hsl]; exact lt_of_le_of_ne (hclosQ l hlmem).1 (Ne.symm hl_ne)
          rcases eq_or_lt_of_le hs.2 with hsu | hsu
          · rw [hsu]; exact lt_of_le_of_ne (hclosQ u humem).1 (Ne.symm hu_ne)
          have h := hgap s ⟨hsl, hsu⟩
          simp only [laneC1RQc, mem_setOf_eq, not_or, not_le] at h
          exact h.1
        · rcases h.2.2.2 hu_ne hl_ne with h' | h'
          · exact Or.inl h'
          · right; rw [h']; norm_num
      exact hdeg (laneC1R_left_deg_zero hβ01 hpos q hq h)
  · 
    push Not at hF
    let β : C(unitInterval, ℂ) :=
      ⟨fun t => τ t, hτ.comp_continuous continuous_subtype_val (fun t => t.2)⟩
    have hβ01 : β 0 = β 1 := by simpa [β] using hclosed
    have hin_quad : ∀ u ∈ Icc (0 : ℝ) 1, 0 < (τ u).re ∧ (τ u).im < 1 := by
      intro u hu
      have h := hF u hu
      simp only [laneC1RQc, mem_setOf_eq, not_or, not_le] at h
      exact h
    have hτS : ∀ v ∈ Icc (0 : ℝ) 1, τ v ∈ (rectAB 1 1).toSet := fun v hv =>
      hσsq_of _ (hτann v hv).2 (hin_quad v hv).1.le (hin_quad v hv).2.le
    have hdegp : ∃ h : ∀ t, β t ≠ p, laneC1RDeg β p h ≠ 0 := by
      have hne : ∀ t, β t ≠ p := by
        intro t heq
        have := (hτann t t.2).1
        simp only [β, ContinuousMap.coe_mk] at heq
        rw [heq] at this
        linarith
      refine ⟨hne, fun hdeg => hMjump ?_⟩
      have key := loopDeg_eq_of_lift (laneC1RSubLoop β p) (laneC1RSubLoop_ne hne)
        (by simp [β, hclosed]) (L := fun t : unitInterval => M t)
        (hM.comp_continuous continuous_subtype_val (fun t => t.2))
        (fun t => by simp [β, hMexp t t.2])
      unfold laneC1RDeg at hdeg
      rw [hdeg] at key
      simpa using key
    refine ⟨τ, 0, 1, β, le_rfl, zero_le_one, le_rfl, hτ, hτann, fun D => le_rfl, hτS, hβ01,
      fun t _ => ⟨t, t.2, rfl⟩, ?_, ?_, ?_⟩
    · exact laneC1R_hin_of_point hβ01 hpS hpc (fun t _ => (hτann t t.2).1) hdegp
    · exact laneC1R_right_deg_zero hβ01 (fun t =>
        laneC1R_re_lt_of_annulus (hτann t t.2).2 hcR)
    · intro q hq h hdeg
      exact absurd (laneC1R_left_deg_zero hβ01 (fun t => Or.inl (hin_quad t t.2).1) q hq h)
        hdeg

end SupercriticalLQGUniqueness.B2.DG20Conc
