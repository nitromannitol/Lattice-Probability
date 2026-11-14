/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RPay at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Mass
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Fatou
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKScale

 















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

attribute [local instance] Classical.propDecidable

 
theorem laneA3R_crossing_piece {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) {c : ℂ}
    {r : ℝ} (hr : 0 < r) (hfar : 2 * r ≤ dist (γ 0) c ∨ 2 * r ≤ dist (γ 1) c) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hvis : dist (γ t) c < r) :
    ∃ a e : ℝ, 0 ≤ a ∧ a ≤ e ∧ e ≤ 1 ∧ (∀ u ∈ Icc a e, dist (γ u) c ∈ Icc r (2 * r)) ∧
      ((γ a ∈ sphere c r ∧ γ e ∈ sphere c (2 * r)) ∨
        (γ e ∈ sphere c r ∧ γ a ∈ sphere c (2 * r))) := by
  set g : ℝ → ℝ := fun u => dist (γ u) c with hgdef
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) :=
    (continuous_id.dist continuous_const).comp_continuousOn hγ
  have hgsub : ∀ {x y : ℝ}, 0 ≤ x → y ≤ 1 → ContinuousOn g (Icc x y) :=
    fun hx hy => hg.mono (Icc_subset_Icc hx hy)
  rcases hfar with h0 | h1
  · 
    set T₁ : Set ℝ := Icc 0 t ∩ g ⁻¹' Ici (2 * r) with hT₁
    have hT₁c : IsClosed T₁ := (hgsub le_rfl ht.2).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Ici
    have hT₁ne : T₁.Nonempty := ⟨0, ⟨le_rfl, ht.1⟩, h0⟩
    have hT₁bdd : BddAbove T₁ := ⟨t, fun u hu => hu.1.2⟩
    set a := sSup T₁
    have haT : a ∈ T₁ := hT₁c.csSup_mem hT₁ne hT₁bdd
    have hale : ∀ u ∈ T₁, u ≤ a := fun u hu => le_csSup hT₁bdd hu
    have ha0 : 0 ≤ a := haT.1.1
    have hat : a ≤ t := haT.1.2
    have hga : g a = 2 * r := by
      obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' hat (hgsub ha0 ht.2)
        ⟨by simp only [g]; linarith, haT.2⟩
      have : u ∈ T₁ := ⟨⟨ha0.trans hu.1, hu.2⟩, by rw [mem_preimage, hgu]; exact mem_Ici.mpr le_rfl⟩
      have hua : u = a := le_antisymm (hale u this) hu.1
      rw [← hua, hgu]
    set T₂ : Set ℝ := Icc a t ∩ g ⁻¹' Iic r with hT₂
    have hT₂c : IsClosed T₂ := (hgsub ha0 ht.2).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
    have hT₂ne : T₂.Nonempty := ⟨t, ⟨hat, le_rfl⟩, mem_Iic.mpr hvis.le⟩
    have hT₂bdd : BddBelow T₂ := ⟨a, fun u hu => hu.1.1⟩
    set e := sInf T₂
    have heT : e ∈ T₂ := hT₂c.csInf_mem hT₂ne hT₂bdd
    have hge : ∀ u ∈ T₂, e ≤ u := fun u hu => csInf_le hT₂bdd hu
    have hae : a ≤ e := heT.1.1
    have het : e ≤ t := heT.1.2
    have hge_r : g e = r := by
      obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' hae (hgsub ha0 (het.trans ht.2))
        ⟨heT.2, by rw [hga]; linarith⟩
      have : u ∈ T₂ := ⟨⟨hu.1, hu.2.trans het⟩, by rw [mem_preimage, hgu]; exact mem_Iic.mpr le_rfl⟩
      have hue : u = e := le_antisymm hu.2 (hge u this)
      rw [← hue, hgu]
    refine ⟨a, e, ha0, hae, het.trans ht.2, fun u hu => ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · by_contra hlt
      push Not at hlt
      have : u ∈ T₂ := ⟨⟨hu.1, hu.2.trans het⟩, mem_Iic.mpr hlt.le⟩
      have hue : u = e := le_antisymm hu.2 (hge u this)
      rw [hue] at hlt
      exact (lt_irrefl r) (hge_r ▸ hlt)
    · by_contra hlt
      push Not at hlt
      have : u ∈ T₁ := ⟨⟨ha0.trans hu.1, hu.2.trans het⟩, mem_Ici.mpr hlt.le⟩
      have hua : u = a := le_antisymm (hale u this) hu.1
      rw [hua] at hlt
      exact (lt_irrefl (2 * r)) (hga ▸ hlt)
    · rw [mem_sphere]; exact hge_r
    · rw [mem_sphere]; exact hga
  · 
    set T₂ : Set ℝ := Icc t 1 ∩ g ⁻¹' Ici (2 * r) with hT₂
    have hT₂c : IsClosed T₂ := (hgsub ht.1 le_rfl).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Ici
    have hT₂ne : T₂.Nonempty := ⟨1, ⟨ht.2, le_rfl⟩, h1⟩
    have hT₂bdd : BddBelow T₂ := ⟨t, fun u hu => hu.1.1⟩
    set e := sInf T₂
    have heT : e ∈ T₂ := hT₂c.csInf_mem hT₂ne hT₂bdd
    have hge : ∀ u ∈ T₂, e ≤ u := fun u hu => csInf_le hT₂bdd hu
    have hte : t ≤ e := heT.1.1
    have he1 : e ≤ 1 := heT.1.2
    have hge2 : g e = 2 * r := by
      obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc hte (hgsub ht.1 he1)
        ⟨by simp only [g]; linarith, heT.2⟩
      have : u ∈ T₂ := ⟨⟨hu.1, hu.2.trans he1⟩, by rw [mem_preimage, hgu]; exact mem_Ici.mpr le_rfl⟩
      have hue : u = e := le_antisymm hu.2 (hge u this)
      rw [← hue, hgu]
    set T₁ : Set ℝ := Icc t e ∩ g ⁻¹' Iic r with hT₁
    have hT₁c : IsClosed T₁ := (hgsub ht.1 he1).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
    have hT₁ne : T₁.Nonempty := ⟨t, ⟨le_rfl, hte⟩, mem_Iic.mpr hvis.le⟩
    have hT₁bdd : BddAbove T₁ := ⟨e, fun u hu => hu.1.2⟩
    set a := sSup T₁
    have haT : a ∈ T₁ := hT₁c.csSup_mem hT₁ne hT₁bdd
    have hale : ∀ u ∈ T₁, u ≤ a := fun u hu => le_csSup hT₁bdd hu
    have hta : t ≤ a := haT.1.1
    have hae : a ≤ e := haT.1.2
    have hga : g a = r := by
      obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc hae (hgsub (ht.1.trans hta) he1)
        ⟨haT.2, by rw [hge2]; linarith⟩
      have : u ∈ T₁ := ⟨⟨hta.trans hu.1, hu.2⟩, by rw [mem_preimage, hgu]; exact mem_Iic.mpr le_rfl⟩
      have hua : u = a := le_antisymm (hale u this) hu.1
      rw [← hua, hgu]
    refine ⟨a, e, ht.1.trans hta, hae, he1, fun u hu => ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩⟩
    · by_contra hlt
      push Not at hlt
      have : u ∈ T₁ := ⟨⟨hta.trans hu.1, hu.2⟩, mem_Iic.mpr hlt.le⟩
      have hua : u = a := le_antisymm (hale u this) hu.1
      rw [hua] at hlt
      exact (lt_irrefl r) (hga ▸ hlt)
    · by_contra hlt
      push Not at hlt
      have : u ∈ T₂ := ⟨⟨hta.trans hu.1, hu.2.trans he1⟩, mem_Ici.mpr hlt.le⟩
      have hue : u = e := le_antisymm hu.2 (hge u this)
      rw [hue] at hlt
      exact (lt_irrefl (2 * r)) (hge2 ▸ hlt)
    · rw [mem_sphere]; exact hga
    · rw [mem_sphere]; exact hge2

 
theorem laneA3R_card_int_window (x : ℝ) (R : ℕ) :
    (Finset.Icc ⌈x - R⌉ ⌊x + R⌋).card ≤ 2 * R + 1 := by
  rw [Int.card_Icc]
  have h1 : (⌊x + R⌋ : ℝ) ≤ x + R := Int.floor_le _
  have h2 : x - R ≤ (⌈x - R⌉ : ℝ) := Int.le_ceil _
  have h3 : ((⌊x + R⌋ - ⌈x - R⌉ : ℤ) : ℝ) ≤ 2 * R := by push_cast; linarith
  have h4 : ⌊x + R⌋ - ⌈x - R⌉ ≤ 2 * (R : ℤ) := by exact_mod_cast h3
  omega

theorem laneA3R_coord_window {y b K : ℝ} (hK : 0 < K) {R : ℝ}
    (h : |y - (b + 1 / 2) / K| ≤ R / K) : b ∈ Icc (y * K - 1 / 2 - R) (y * K - 1 / 2 + R) := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : (b + 1 / 2) / K = (b + 1 / 2) * K⁻¹ := div_eq_mul_inv _ _
  constructor
  · have : y * K - (b + 1 / 2) ≤ R := by
      have := mul_le_mul_of_nonneg_right h2 hK.le
      rw [sub_mul, div_mul_cancel₀ _ hK.ne', div_mul_cancel₀ _ hK.ne'] at this
      linarith
    linarith
  · have : -R ≤ y * K - (b + 1 / 2) := by
      have := mul_le_mul_of_nonneg_right h1 hK.le
      rw [sub_mul, div_mul_cancel₀ _ hK.ne', neg_mul, div_mul_cancel₀ _ hK.ne'] at this
      linarith
    linarith

 
theorem laneA3R_overlap_card {K m : ℕ} (hm : m ≤ K) (s : Finset (ℤ × ℤ)) (q : ℂ) :
    (s.filter fun b => q ∈ j1SourceCross K m b).card ≤ (4 * 2 ^ m + 1) ^ 2 := by
  set R : ℕ := 2 * 2 ^ m with hR
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  have hrad : 2 * LaneCInputs.sourceRadius K m = (R : ℝ) / 2 ^ K := by
    unfold LaneCInputs.sourceRadius
    rw [hR]
    push_cast
    have h2 : (2 : ℝ) ^ K = 2 ^ (K - m) * 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    rw [h2, inv_pow]
    field_simp
  set x₁ : ℝ := q.re * 2 ^ K - 1 / 2
  set x₂ : ℝ := q.im * 2 ^ K - 1 / 2
  have hsub : s.filter (fun b => q ∈ j1SourceCross K m b) ⊆
      Finset.Icc ⌈x₁ - R⌉ ⌊x₁ + R⌋ ×ˢ Finset.Icc ⌈x₂ - R⌉ ⌊x₂ + R⌋ := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have hd : dist q (T20.dyCenter K b) ≤ 2 * LaneCInputs.sourceRadius K m := hb.2.2
    rw [hrad] at hd
    have hre : |q.re - (T20.dyCenter K b).re| ≤ (R : ℝ) / 2 ^ K :=
      (Complex.abs_re_le_norm (q - T20.dyCenter K b)).trans (by rw [← dist_eq_norm]; exact hd)
    have him : |q.im - (T20.dyCenter K b).im| ≤ (R : ℝ) / 2 ^ K :=
      (Complex.abs_im_le_norm (q - T20.dyCenter K b)).trans (by rw [← dist_eq_norm]; exact hd)
    have hcre : (T20.dyCenter K b).re = ((b.1 : ℝ) + 1 / 2) / 2 ^ K := by
      simp [T20.dyCenter, div_eq_mul_inv, inv_pow]
    have hcim : (T20.dyCenter K b).im = ((b.2 : ℝ) + 1 / 2) / 2 ^ K := by
      simp [T20.dyCenter, div_eq_mul_inv, inv_pow]
    rw [hcre] at hre
    rw [hcim] at him
    have w1 := laneA3R_coord_window hK hre
    have w2 := laneA3R_coord_window hK him
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨Int.ceil_le.mpr w1.1, Int.le_floor.mpr w1.2⟩, ⟨Int.ceil_le.mpr w2.1, Int.le_floor.mpr w2.2⟩⟩
  calc (s.filter fun b => q ∈ j1SourceCross K m b).card
      ≤ (Finset.Icc ⌈x₁ - R⌉ ⌊x₁ + R⌋ ×ˢ Finset.Icc ⌈x₂ - R⌉ ⌊x₂ + R⌋).card :=
        Finset.card_le_card hsub
    _ = (Finset.Icc ⌈x₁ - R⌉ ⌊x₁ + R⌋).card * (Finset.Icc ⌈x₂ - R⌉ ⌊x₂ + R⌋).card :=
        Finset.card_product _ _
    _ ≤ (2 * R + 1) * (2 * R + 1) :=
        Nat.mul_le_mul (laneA3R_card_int_window x₁ R) (laneA3R_card_int_window x₂ R)
    _ = (4 * 2 ^ m + 1) ^ 2 := by rw [hR]; ring

 


theorem laneA3R_hit_payment {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (ξ : ℝ) (f : ℂ → ℝ) {K m : ℕ} (hr4 : 4 * LaneCInputs.sourceRadius K m < 1)
    (s : Finset (ℤ × ℤ)) (N : ℕ)
    (hcard : ∀ q : ℂ, (s.filter fun b => q ∈ j1SourceCross K m b).card ≤ N)
    (hhit : ∀ b ∈ s, ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ laneCHitBall K m b) :
    ∑ b ∈ s, crossLenIn ξ f (j1SourceCross K m b) (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b) ≤ (N : ℝ≥0∞) * lfppLen ξ f γ := by
  obtain ⟨z₀, hz₀, z₁, hz₁, hpath, -⟩ := hγ
  have h0 : γ 0 ∈ (rectAB 1 1).side₁ := by simpa only [hpath.source] using hz₀
  have h1 : γ 1 ∈ (rectAB 1 1).side₂ := by simpa only [hpath.target] using hz₁
  have hr0 : 0 < LaneCInputs.sourceRadius K m := by
    unfold LaneCInputs.sourceRadius; positivity
  apply laneA3_across_mass_of_crossing_pieces s _ _ _ γ hpath ξ f N hcard
  intro b hb
  obtain ⟨t, ht, htb⟩ := hhit b hb
  have hfar : 2 * LaneCInputs.sourceRadius K m ≤ dist (γ 0) (T20.dyCenter K b) ∨
      2 * LaneCInputs.sourceRadius K m ≤ dist (γ 1) (T20.dyCenter K b) := by
    by_contra hcon
    push Not at hcon
    have hre : (γ 1).re - (γ 0).re = 1 := by
      rw [(mem_rectAB_side₂.mp h1).1, (mem_rectAB_side₁.mp h0).1]; ring
    have hd : 1 ≤ dist (γ 1) (γ 0) := by
      have h := Complex.abs_re_le_norm (γ 1 - γ 0)
      rw [Complex.sub_re, hre, abs_one, ← dist_eq_norm] at h
      exact h
    have := dist_triangle_right (γ 1) (γ 0) (T20.dyCenter K b)
    linarith
  obtain ⟨a, e, ha0, hae, he1, hrange, hends⟩ :=
    laneA3R_crossing_piece hpath.continuousOn hr0 hfar ht (mem_ball.mp htb)
  exact ⟨a, e, ha0, hae, he1, fun u hu => hrange u hu, hends⟩

 

theorem laneA3R_eventual_hit_mass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ) (n K m : ℕ)
    (hr4 : 4 * LaneCInputs.sourceRadius K m < 1)
    (γ : ℕ → ℕ → Ω → ℝ → ℂ)
    (hγ : ∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j))
    (s : Finset (ℤ × ℤ)) (N : ℕ)
    (hcard : ∀ q : ℂ, (s.filter fun b => q ∈ j1SourceCross K m b).card ≤ N) (ω : Ω) :
    ∑ b ∈ s, (laneCEventualHit γ n K m b).indicator
        (fun x => crossLenIn ξ (fun z => psiMN Q W P 0 n z x) (j1SourceCross K m b)
          (LaneCInputs.sourceInner K m b) (LaneCInputs.sourceOuter K m b)) ω ≤
      (N : ℝ≥0∞) * rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
  set L : ℝ≥0∞ := rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) with hLdef
  set A : ℤ × ℤ → ℝ≥0∞ := fun b => crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
    (j1SourceCross K m b) (LaneCInputs.sourceInner K m b) (LaneCInputs.sourceOuter K m b)
  have hind : ∀ b, (laneCEventualHit γ n K m b).indicator
      (fun x => crossLenIn ξ (fun z => psiMN Q W P 0 n z x) (j1SourceCross K m b)
        (LaneCInputs.sourceInner K m b) (LaneCInputs.sourceOuter K m b)) ω =
      if ω ∈ laneCEventualHit γ n K m b then A b else 0 := fun b => by
    rw [Set.indicator_apply]
  simp only [hind]
  by_cases hcase : N ≠ 0 ∧ L = ⊤
  · rw [hcase.2, ENNReal.mul_top (by exact_mod_cast hcase.1)]
    exact le_top
  have hη : Tendsto (fun j : ℕ => (((j : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfac : Tendsto (fun j : ℕ => ENNReal.ofReal (1 + (((j : ℝ) + 1)⁻¹)))
      atTop (nhds (1 : ℝ≥0∞)) := by
    have hr : Tendsto (fun j : ℕ => 1 + (((j : ℝ) + 1)⁻¹)) atTop (nhds (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.add hη)
    simpa using ENNReal.tendsto_ofReal hr
  have hcost : Tendsto (fun j : ℕ => (N : ℝ≥0∞) * ENNReal.ofReal (1 + (((j : ℝ) + 1)⁻¹)) * L)
      atTop (nhds ((N : ℝ≥0∞) * L)) := by
    by_cases hN : N = 0
    · subst hN
      simp only [Nat.cast_zero, zero_mul]
      exact tendsto_const_nhds
    have hLtop : L ≠ ⊤ := fun h => hcase ⟨hN, h⟩
    have hfirst : Tendsto (fun j : ℕ => (N : ℝ≥0∞) * ENNReal.ofReal (1 + (((j : ℝ) + 1)⁻¹)))
        atTop (nhds (N : ℝ≥0∞)) := by
      convert ENNReal.Tendsto.mul tendsto_const_nhds
        (Or.inr (by simp : (1 : ℝ≥0∞) ≠ ⊤)) hfac
        (Or.inl (by simp : (1 : ℝ≥0∞) ≠ 0)) using 1 <;> simp
    exact ENNReal.Tendsto.mul hfirst (Or.inr hLtop) tendsto_const_nhds (Or.inr (by simp))
  apply laneA3_eventual_visit_mass_of_near_cost s (fun j b => ω ∈ laneCHits γ j n K m b) A
    (fun b => ω ∈ laneCEventualHit γ n K m b) (fun b _ h => h) _ _ ?_ hcost
  intro j
  rw [← Finset.sum_filter]
  calc ∑ b ∈ s.filter (fun b => ω ∈ laneCHits γ j n K m b), A b
      ≤ (N : ℝ≥0∞) * lfppLen ξ (fun x => psiMN Q W P 0 n x ω) (γ j n ω) := by
        apply laneA3R_hit_payment ((hγ j).adm n ω) ξ _ hr4 _ N
        · intro q
          exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ s))).trans
            (hcard q)
        · intro b hb
          exact (Finset.mem_filter.mp hb).2
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal (1 + (((j : ℝ) + 1)⁻¹)) * L) :=
        mul_le_mul_right ((hγ j).near n ω) _
    _ = (N : ℝ≥0∞) * ENNReal.ofReal (1 + (((j : ℝ) + 1)⁻¹)) * L := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
