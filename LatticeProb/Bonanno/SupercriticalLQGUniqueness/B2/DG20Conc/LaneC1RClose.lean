/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RClose at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RBranch

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def laneC1RArcPath (σ : ℝ → ℂ) (l u : ℝ) (hlu : l ≤ u) (hσ : ContinuousOn σ (Icc l u)) :
    Path (σ l) (σ u) where
  toFun t := σ (l + (t : ℝ) * (u - l))
  continuous_toFun := hσ.comp_continuous (by fun_prop) (fun t => by
    have h0 : 0 ≤ (t : ℝ) := t.2.1
    have h1 : (t : ℝ) ≤ 1 := t.2.2
    constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.mpr hlu)])
  source' := by simp
  target' := by simp

theorem laneC1R_arc_param_mem {l u : ℝ} (hlu : l ≤ u) (t : unitInterval) :
    l + (t : ℝ) * (u - l) ∈ Icc l u := by
  have h0 : 0 ≤ (t : ℝ) := t.2.1
  have h1 : (t : ℝ) ≤ 1 := t.2.2
  constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.mpr hlu)]

theorem laneC1RArcPath_range {σ : ℝ → ℂ} {l u : ℝ} {hlu : l ≤ u}
    {hσ : ContinuousOn σ (Icc l u)} {z : ℂ} (hz : z ∈ range (laneC1RArcPath σ l u hlu hσ)) :
    ∃ s ∈ Icc l u, z = σ s := by
  obtain ⟨t, rfl⟩ := hz
  exact ⟨_, laneC1R_arc_param_mem hlu t, rfl⟩

 
theorem laneC1R_closed_jump_deg {σ Λ : ℝ → ℂ} {p : ℂ} {l u : ℝ} (hlu : l ≤ u)
    (hσ : ContinuousOn σ (Icc l u)) (hΛ : ContinuousOn Λ (Icc l u))
    (hΛexp : ∀ s ∈ Icc l u, Complex.exp (Λ s) = σ s - p)
    (ext : Path (σ u) (σ l)) {B : ℂ → ℂ} {E : Set ℂ} (hB : ContinuousOn B E)
    (hBexp : ∀ z ∈ E, Complex.exp (B z) = z - p) (hextE : ∀ t, ext t ∈ E)
    (hjump : Λ u - Λ l ≠ B (σ u) - B (σ l)) :
    ∃ h : ∀ t, ((laneC1RArcPath σ l u hlu hσ).trans ext) t ≠ p,
      laneC1RDeg ((laneC1RArcPath σ l u hlu hσ).trans ext) p h ≠ 0 := by
  set β := (laneC1RArcPath σ l u hlu hσ).trans ext with hβdef
  let ΛP : Path (Λ l) (Λ u) :=
    { toFun := fun t => Λ (l + (t : ℝ) * (u - l))
      continuous_toFun := hΛ.comp_continuous (by fun_prop) (laneC1R_arc_param_mem hlu)
      source' := by simp
      target' := by simp }
  have hBext : Continuous fun t => B (ext t) :=
    hB.comp_continuous ext.continuous hextE
  set C : ℂ := Λ u - B (σ u) with hCdef
  let BP : Path (Λ u) (B (σ l) + C) :=
    { toFun := fun t => B (ext t) + C
      continuous_toFun := hBext.add continuous_const
      source' := by
        show B (ext 0) + C = Λ u
        rw [ext.source, hCdef]
        ring
      target' := by
        show B (ext 1) + C = B (σ l) + C
        rw [ext.target] }
  have hσu : σ u - p ≠ 0 := by
    rw [← hΛexp u ⟨hlu, le_rfl⟩]
    exact Complex.exp_ne_zero _
  have hexpC : Complex.exp C = 1 := by
    rw [hCdef, Complex.exp_sub, hΛexp u ⟨hlu, le_rfl⟩,
      hBexp _ (by simpa [ext.source] using hextE 0), div_self hσu]
  have hlift : ∀ t, Complex.exp ((ΛP.trans BP) t) = β t - p := by
    intro t
    rw [hβdef, Path.trans_apply, Path.trans_apply]
    split_ifs with h
    · exact hΛexp _ (laneC1R_arc_param_mem hlu _)
    · show Complex.exp (B (ext _) + C) = ext _ - p
      rw [Complex.exp_add, hexpC, mul_one, hBexp _ (hextE _)]
  have hne : ∀ t, β t ≠ p := by
    intro t heq
    have := hlift t
    rw [heq, sub_self] at this
    exact Complex.exp_ne_zero _ this
  refine ⟨hne, ?_⟩
  intro hdeg
  have key := loopDeg_eq_of_lift (laneC1RSubLoop β p) (laneC1RSubLoop_ne hne)
    (by simp [β]) (L := ΛP.trans BP) (ΛP.trans BP).continuous hlift
  unfold laneC1RDeg at hdeg
  rw [hdeg, Path.target, Path.source] at key
  apply hjump
  simp only [Int.cast_zero, zero_mul] at key
  rw [hCdef] at key
  linear_combination key

end SupercriticalLQGUniqueness.B2.DG20Conc
