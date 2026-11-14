/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RQuadrant at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RSepData

 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex Metric QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

 
theorem laneC1R_exists_inner_reference {q c : ℂ} {r : ℝ} (hq : q ∈ (rectAB 1 1).toSet)
    (hqc : dist q c < r) :
    ∃ p : ℂ, p ∈ (rectAB 1 1).toSet ∧ 0 < p.re ∧ p.im < 1 ∧ dist p c < r := by
  rw [mem_rectAB_toSet] at hq
  set ε : ℝ := min (1 / 2) ((r - dist q c) / 2) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ (r - dist q c) / 2 := min_le_right _ _
  set h₀ : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * I with hh₀
  set p : ℂ := q + (ε : ℂ) * (h₀ - q) with hp
  have hpre : p.re = (1 - ε) * q.re + ε / 2 := by simp [hp, hh₀]; ring
  have hpim : p.im = (1 - ε) * q.im + ε / 2 := by simp [hp, hh₀]; ring
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [mem_rectAB_toSet, hpre, hpim]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]
  · rw [hpre]; nlinarith [hq.1.1]
  · rw [hpim]; nlinarith [hq.2.2]
  · have hpq : dist p q ≤ ε := by
      rw [dist_eq_norm, hp, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε0]
      have hn : ‖h₀ - q‖ ≤ 1 := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have hre : |(h₀ - q).re| ≤ 1 / 2 := by
          rw [abs_le]; simp [hh₀]; constructor <;> linarith [hq.1.1, hq.1.2]
        have him : |(h₀ - q).im| ≤ 1 / 2 := by
          rw [abs_le]; simp [hh₀]; constructor <;> linarith [hq.2.1, hq.2.2]
        linarith
      nlinarith
    linarith [dist_triangle p q c]

 
theorem laneC1R_quadrant_detour (D : ContMetric) {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ x ∈ Icc a b, r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b) (sphere c r) (sphere c (2 * r)))
    (hcR : c.re + 2 * r ≤ 1) (hcB : 2 * r ≤ c.im)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    (hγ0 : γ 0 ∈ (rectAB 1 1).side₁) (hγ1 : γ 1 ∈ (rectAB 1 1).side₂)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hvisit : dist (γ m) c < r) :
    ∃ (α : ℝ → ℂ) (t₀ t₁ : ℝ), ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, r < dist (α t) c ∧ dist (α t) c < 2 * r) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet) ∧
      D.len α 0 1 ≤ D.len ρ a b ∧
      t₀ ∈ Icc (0 : ℝ) 1 ∧ t₁ ∈ Icc (0 : ℝ) 1 ∧ t₀ ≤ t₁ ∧
      ((γ t₀ = α 0 ∧ ∀ t ∈ Icc (0 : ℝ) t₀, r ≤ dist (γ t) c) ∨
        (t₀ = 0 ∧ α 0 ∈ (rectAB 1 1).side₁)) ∧
      ((γ t₁ = α 1 ∧ ∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c) ∨
        (t₁ = 1 ∧ α 1 ∈ (rectAB 1 1).side₂)) := by
  
  have hv : 2 * r ≤ dist (c + ((2 * r : ℝ) : ℂ)) c := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  obtain ⟨τ, hτ, hτann, hτclosed, hτcost, G, hG, hGdef, hGdeg⟩ :=
    laneC_exists_paid_essential_loop D hab hρ hr hρann hv hsep
  
  obtain ⟨p, hpS, hp0, hp1, hpc⟩ := laneC1R_exists_inner_reference (hγS m hm) hvisit
  let βτ : C(unitInterval, ℂ) :=
    ⟨fun t => τ t, hτ.comp_continuous continuous_subtype_val (fun t => t.2)⟩
  have hβτ : βτ 0 = βτ 1 := by simpa [βτ] using hτclosed
  have hseg : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1, βτ t ≠ c + (s : ℂ) * (p - c) := by
    intro t s hs heq
    have h1 := (hτann t t.2).1
    have hd : dist (c + (s : ℂ) * (p - c)) c ≤ dist p c := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hs.1, dist_eq_norm]
      nlinarith [norm_nonneg (p - c), hs.2]
    have : dist (τ t) c ≤ dist p c := by
      have h' : τ t = c + (s : ℂ) * (p - c) := heq
      rw [h']
      exact hd
    linarith
  have hcne : ∀ t, βτ t ≠ c := fun t => by simpa using hseg t 0 ⟨le_rfl, zero_le_one⟩
  have hpne : ∀ t, βτ t ≠ p := fun t => by simpa using hseg t 1 ⟨zero_le_one, le_rfl⟩
  have hdegc : laneC1RDeg βτ c hcne ≠ 0 := by
    have e : laneC1RSubLoop βτ c = G := by
      ext t
      simp [βτ, hGdef]
    unfold laneC1RDeg
    rw [laneC1R_loopDeg_congr e _ hG]
    exact hGdeg
  have hdegp : laneC1RDeg βτ p hpne ≠ 0 := by
    have e := laneC1R_deg_eq_of_segment hβτ hseg hcne hpne
    rw [← e]
    exact hdegc
  
  obtain ⟨Mu, hMu⟩ := exists_lift_exp (laneC1RSubLoop βτ p) (laneC1RSubLoop_ne hpne)
  have hMujump : Mu 1 - Mu 0 ≠ 0 := by
    intro h0
    have key := loopDeg_eq_of_lift (laneC1RSubLoop βτ p) (laneC1RSubLoop_ne hpne)
      (by simp [βτ, hτclosed]) Mu.continuous hMu
    rw [h0] at key
    apply hdegp
    unfold laneC1RDeg
    have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := two_pi_I_ne_zero'
    exact_mod_cast (mul_eq_zero.mp key.symm).resolve_right h2
  let Mr : C(ℝ, ℂ) := ContinuousMap.IccExtend (zero_le_one' ℝ) Mu
  have hMr : ContinuousOn (fun x : ℝ => Mr x) (Icc (0 : ℝ) 1) := Mr.continuous.continuousOn
  have hMrexp : ∀ x ∈ Icc (0 : ℝ) 1, Complex.exp (Mr x) = τ x - p := by
    intro x hx
    have hval : Mr x = Mu ⟨x, hx⟩ := Set.IccExtend_of_mem (zero_le_one' ℝ) Mu hx
    rw [hval, hMu]
    rfl
  have hMr0 : Mr 0 = Mu 0 :=
    Set.IccExtend_of_mem (zero_le_one' ℝ) Mu (show (0 : ℝ) ∈ Icc 0 1 by simp)
  have hMr1 : Mr 1 = Mu 1 :=
    Set.IccExtend_of_mem (zero_le_one' ℝ) Mu (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hMrjump : Mr 1 - Mr 0 ≠ 0 := by rw [hMr0, hMr1]; exact hMujump
  
  obtain ⟨σ, a₁, a₂, β, ha₁, ha₁₂, ha₂, hσc, hσann, hσcost, hσS, hβ01, hβS, hin, hR, hL⟩ :=
    laneC1R_quadrant_sepdata hτ hτclosed hτann hcR hcB hp0 hp1 hpS hpc hMr hMrexp hMrjump
  have hsub : Icc a₁ a₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha₁ ha₂
  obtain ⟨v₀, hv₀, v₁, hv₁, t₀, t₁, ht₀, ht₁, ht₀₁, hstart, hend⟩ :=
    laneC1R_safe_hits ha₁₂ (hσc.mono hsub) (fun v hv => (hσann v (hsub hv)).1) β hβ01 hβS
      hin hR hL hγ hγS hγ0 hγ1 hm hvisit
  let α := SupercriticalLQGUniqueness.B2.Strong.seg σ v₀ v₁
  refine ⟨α, t₀, t₁, ?_, ?_, ?_, ?_, ht₀, ht₁, ht₀₁, ?_, ?_⟩
  · exact SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hσc (hsub hv₀) (hsub hv₁)
  · intro t ht
    exact hσann _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem (hsub hv₀) (hsub hv₁) ht)
  · intro t ht
    exact hσS _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hv₀ hv₁ ht)
  · exact ((SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le (D.pt ∘ σ)
      (hsub hv₀) (hsub hv₁)).trans (hσcost D)).trans hτcost
  · simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg_zero] using hstart
  · simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg_one] using hend

end SupercriticalLQGUniqueness.B2.DG20Conc
