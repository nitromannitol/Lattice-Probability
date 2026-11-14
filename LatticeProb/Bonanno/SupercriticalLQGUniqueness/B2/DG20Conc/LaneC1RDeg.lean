/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDeg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def laneC1RSubLoop (β : C(unitInterval, ℂ)) (q : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => β t - q, by fun_prop⟩

@[simp] theorem laneC1RSubLoop_apply (β : C(unitInterval, ℂ)) (q : ℂ)
    (t : unitInterval) : laneC1RSubLoop β q t = β t - q := rfl

theorem laneC1RSubLoop_ne {β : C(unitInterval, ℂ)} {q : ℂ}
    (h : ∀ t, β t ≠ q) (t : unitInterval) : laneC1RSubLoop β q t ≠ 0 :=
  sub_ne_zero.mpr (h t)

 
def laneC1RDeg (β : C(unitInterval, ℂ)) (q : ℂ) (h : ∀ t, β t ≠ q) : ℤ :=
  loopDeg (laneC1RSubLoop β q) (laneC1RSubLoop_ne h)

theorem laneC1R_loopDeg_congr {γ δ : C(unitInterval, ℂ)} (e : γ = δ)
    (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0) : loopDeg γ hγ = loopDeg δ hδ := by
  subst e
  rfl

theorem laneC1RDeg_congr {β : C(unitInterval, ℂ)} {q q' : ℂ} (e : q = q')
    (h : ∀ t, β t ≠ q) (h' : ∀ t, β t ≠ q') :
    laneC1RDeg β q h = laneC1RDeg β q' h' := by
  subst e
  rfl

 
theorem laneC1R_deg_eq_of_path {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1)
    (σ : C(unitInterval, ℂ)) (hσ : ∀ t s, β t ≠ σ s) :
    laneC1RDeg β (σ 0) (fun t => hσ t 0) = laneC1RDeg β (σ 1) (fun t => hσ t 1) := by
  let H : C(unitInterval × unitInterval, ℂ) := ⟨fun p => β p.1 - σ p.2, by fun_prop⟩
  have h0 : ∀ p, H p ≠ 0 := fun p => sub_ne_zero.mpr (hσ p.1 p.2)
  have hc : ∀ s, H (0, s) = H (1, s) := fun s => by simp [H, hβ]
  have key := loopDeg_homotopy H h0 hc
  have e0 : slice H 0 = laneC1RSubLoop β (σ 0) := by
    ext t
    simp [slice, H]
  have e1 : slice H 1 = laneC1RSubLoop β (σ 1) := by
    ext t
    simp [slice, H]
  exact (laneC1R_loopDeg_congr e0 _ _).symm.trans (key.trans (laneC1R_loopDeg_congr e1 _ _))

 
theorem laneC1R_deg_eq_of_realPath {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hav : ∀ t, ∀ s ∈ Icc a b, β t ≠ γ s) :
    laneC1RDeg β (γ a) (fun t => hav t a ⟨le_rfl, hab⟩) =
      laneC1RDeg β (γ b) (fun t => hav t b ⟨hab, le_rfl⟩) := by
  have hmem : ∀ u : unitInterval, a + (u : ℝ) * (b - a) ∈ Icc a b := by
    intro u
    have hu0 : 0 ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    constructor <;> nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hab)]
  let σ : C(unitInterval, ℂ) :=
    ⟨fun u => γ (a + (u : ℝ) * (b - a)),
      hγ.comp_continuous (by fun_prop) hmem⟩
  have hσ : ∀ t s, β t ≠ σ s := fun t s => hav t _ (hmem s)
  have key := laneC1R_deg_eq_of_path hβ σ hσ
  have e0 : σ 0 = γ a := by simp [σ]
  have e1 : σ 1 = γ b := by simp [σ]
  exact (laneC1RDeg_congr e0 _ _).symm.trans (key.trans (laneC1RDeg_congr e1 _ _))

 
theorem laneC1R_deg_eq_of_segment {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1)
    {q₀ q₁ : ℂ} (hav : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1, β t ≠ q₀ + (s : ℂ) * (q₁ - q₀))
    (h₀ : ∀ t, β t ≠ q₀) (h₁ : ∀ t, β t ≠ q₁) :
    laneC1RDeg β q₀ h₀ = laneC1RDeg β q₁ h₁ := by
  have hγ : ContinuousOn (fun s : ℝ => q₀ + (s : ℂ) * (q₁ - q₀)) (Icc (0 : ℝ) 1) := by
    fun_prop
  have key := laneC1R_deg_eq_of_realPath hβ zero_le_one hγ hav
  have e0 : q₀ + ((0 : ℝ) : ℂ) * (q₁ - q₀) = q₀ := by simp
  have e1 : q₀ + ((1 : ℝ) : ℂ) * (q₁ - q₀) = q₁ := by simp
  exact (laneC1RDeg_congr e0.symm _ _).trans (key.trans (laneC1RDeg_congr e1 _ _))

 
theorem laneC1R_deg_eq_zero_of_far {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1) {q : ℂ}
    (hfar : ∀ t, ‖β t‖ < ‖q‖) (h : ∀ t, β t ≠ q) : laneC1RDeg β q h = 0 := by
  have hq : -q ≠ 0 := by
    intro h0
    have h1 := hfar 0
    rw [neg_eq_zero.mp h0, norm_zero] at h1
    exact (norm_nonneg _).not_gt h1
  have e := loopDeg_eq_of_norm_sub_lt (laneC1RSubLoop β q)
    (ContinuousMap.const unitInterval (-q)) (laneC1RSubLoop_ne h) (fun _ => hq)
    (by simp [hβ]) rfl (fun t => by simpa [norm_neg] using hfar t)
  unfold laneC1RDeg
  rw [e, loopDeg_const (-q) hq]

 
theorem laneC1R_deg_eq_zero_of_ray {β : C(unitInterval, ℂ)} (hβ : β 0 = β 1) {q w : ℂ}
    (hw : w ≠ 0) (hray : ∀ t, ∀ s : ℝ, 0 ≤ s → β t ≠ q + (s : ℂ) * w)
    (h : ∀ t, β t ≠ q) : laneC1RDeg β q h = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_range β.continuous).isBounded.exists_norm_le
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set S₀ : ℝ := (|R| + ‖q‖ + 1) / ‖w‖ with hS₀
  have hS₀nn : 0 ≤ S₀ := by positivity
  have hseg : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1,
      β t ≠ q + (s : ℂ) * ((q + (S₀ : ℂ) * w) - q) := by
    intro t s hs
    have e : q + (s : ℂ) * ((q + (S₀ : ℂ) * w) - q) = q + ((s * S₀ : ℝ) : ℂ) * w := by
      push_cast
      ring
    rw [e]
    exact hray t _ (mul_nonneg hs.1 hS₀nn)
  have hend : ∀ t, β t ≠ q + (S₀ : ℂ) * w := by
    intro t
    have := hray t S₀ hS₀nn
    exact this
  rw [laneC1R_deg_eq_of_segment hβ hseg h hend]
  apply laneC1R_deg_eq_zero_of_far hβ
  intro t
  have hβt : ‖β t‖ ≤ |R| := (hR _ ⟨t, rfl⟩).trans (le_abs_self R)
  have hmul : ‖(S₀ : ℂ) * w‖ = |R| + ‖q‖ + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS₀nn, hS₀]
    field_simp
  have htri : ‖(S₀ : ℂ) * w‖ ≤ ‖q + (S₀ : ℂ) * w‖ + ‖q‖ := by
    have := norm_sub_le (q + (S₀ : ℂ) * w) q
    simpa using this
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
