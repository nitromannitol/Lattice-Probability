/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellScaling.Scaling and Model at commit fdb5cad;
   selected declarations and their proof closure, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Pointwise

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- The **raw scaled-grid event** (the body of `CellularEmbedding.ScaledGridControl`,
transported by the joint-scaling identity) for a multigraph `G` on `ℤ` and an arbitrary cell map `J`; for a cellular embedding
`H` it is `H.ScaledGridControl` (`scaledGridControl_iff_raw`). -/
def RawScaledGridControl {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) (R ε χ β q ρ p : ℝ) : Prop :=
  (∀ x, (J x ∩ ball 0 (ρ * R)).Nonempty → diam (J x) ≤ R * ε ^ q) ∧
    ∀ m n k : ℤ, (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) ∈ ball (0 : ℂ) (ρ * R) →
      R * ε ^ β ≤ R * ε ^ χ * k → R * ε ^ χ * k ≤ ρ * R →
      ball (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (2 * (R * ε ^ χ * k)) ⊆
        ball (0 : ℂ) (ρ * R) →
      ∀ x ∈ verticesMeeting J
          (sphere (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (R * ε ^ χ * k)),
        ENNReal.ofReal p ≤ G.walkLaw x {ω | G.AnnularEvent J
          (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (R * ε ^ χ * k) (G.vertexPath ω)}

theorem scaledGridControl_iff_raw {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (R ε χ β q ρ p : ℝ) :
    H.ScaledGridControl R ε χ β q ρ p ↔ RawScaledGridControl G H.cell R ε χ β q ρ p := Iff.rfl

section Dilation

variable {c : ℝ}

theorem smul_ball_pos (hc : 0 < c) (z : ℂ) (r : ℝ) : c • ball z r = ball (c • z) (c * r) := by
  rw [_root_.smul_ball (ne_of_gt hc), Real.norm_of_nonneg (le_of_lt hc)]

theorem smul_sphere_pos (hc : 0 < c) (z : ℂ) (r : ℝ) : c • sphere z r = sphere (c • z) (c * r) := by
  rw [smul_sphere' (ne_of_gt hc), Real.norm_of_nonneg (le_of_lt hc)]

theorem smul_annulus_pos (hc : 0 < c) (z : ℂ) (r s : ℝ) :
    c • annulus z r s = annulus (c • z) (c * r) (c * s) := by
  unfold annulus
  rw [Set.smul_set_sdiff₀ (ne_of_gt hc), smul_ball_pos hc, smul_ball_pos hc]

theorem inter_smul_nonempty_iff (hc : 0 < c) (A S : Set ℂ) :
    (c⁻¹ • A ∩ S).Nonempty ↔ (A ∩ c • S).Nonempty := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have h : c⁻¹ • A ∩ S = c⁻¹ • (A ∩ c • S) := by
    rw [Set.smul_set_inter₀ (inv_ne_zero hc0), inv_smul_smul₀ hc0]
  rw [h, Set.smul_set_nonempty]

theorem verticesMeeting_smul (hc : 0 < c) (J : ℤ → Set ℂ) (S : Set ℂ) :
    verticesMeeting (fun x => c⁻¹ • J x) S = verticesMeeting J (c • S) := by
  ext x
  exact inter_smul_nonempty_iff hc (J x) S

theorem smul_subset_iff_pos (hc : 0 < c) (A S : Set ℂ) : c⁻¹ • A ⊆ S ↔ A ⊆ c • S := by
  rw [Set.smul_set_subset_iff₀ (inv_ne_zero (ne_of_gt hc)), inv_inv]

theorem diam_inv_smul (hc : 0 < c) (A : Set ℂ) : diam (c⁻¹ • A) = c⁻¹ * diam A := by
  rw [diam_smul₀, Real.norm_of_nonneg (le_of_lt (inv_pos.2 hc))]

end Dilation

/-! ### Dilation covariance of the annular event and of the scaled-grid estimate event -/

theorem annularEvent_smul_iff {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) {c : ℝ} (hc : 0 < c)
    (z : ℂ) (r : ℝ) (X : ℕ → ℤ) :
    G.AnnularEvent (fun x => c⁻¹ • J x) z r X ↔ G.AnnularEvent J (c • z) (c * r) X := by
  unfold LFMultigraph.AnnularEvent
  simp only [verticesMeeting_smul hc, smul_annulus_pos hc, smul_sphere_pos hc, smul_subset_iff_pos hc]
  have e1 : c * (r / 2) = c * r / 2 := by ring
  have e2 : c * (3 * r / 2) = 3 * (c * r) / 2 := by ring
  have e3 : c * (3 * r / 4) = 3 * (c * r) / 4 := by ring
  have e4 : c * (5 * r / 4) = 5 * (c * r) / 4 := by ring
  have e5 : c * (r / 3) = c * r / 3 := by ring
  have e6 : c * (5 * r / 3) = 5 * (c * r) / 3 := by ring
  rw [e1, e2, e3, e4, e5, e6]

theorem rawScaledGridControl_of_smul {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) {c : ℝ}
    (hc : 0 < c) {R ε χ β q ρ p : ℝ} (h : RawScaledGridControl G (fun x => c⁻¹ • J x) R ε χ β q ρ p) :
    RawScaledGridControl G J (c * R) ε χ β q ρ p := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, fun m n k hz hβ hρ hball x hx => ?_⟩
  · have hx' : (c⁻¹ • J x ∩ ball 0 (ρ * R)).Nonempty := by
      rw [inter_smul_nonempty_iff hc, smul_ball_pos hc, smul_zero]
      convert hx using 3
      ring
    have hd := h1 x hx'
    rw [diam_inv_smul hc] at hd
    have := (inv_mul_le_iff₀ hc).1 hd
    calc diam (J x) ≤ c * (R * ε ^ q) := this
      _ = c * R * ε ^ q := by ring
  · set w : ℂ := (m : ℂ) + (n : ℂ) * Complex.I
    set z' : ℂ := ((R * ε ^ χ : ℝ) : ℂ) * w with hz'
    have hzc : ((c * R * ε ^ χ : ℝ) : ℂ) * w = c • z' := by
      rw [hz', Complex.real_smul]; push_cast; ring
    have hrc : c * R * ε ^ χ * k = c * (R * ε ^ χ * k) := by ring
    rw [hzc] at hz hball hx ⊢
    rw [hrc] at hball hx ⊢
    have hz' : z' ∈ ball (0 : ℂ) (ρ * R) := by
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hc)] at hz
      nlinarith
    have hβ' : R * ε ^ β ≤ R * ε ^ χ * k := by nlinarith
    have hρ' : R * ε ^ χ * k ≤ ρ * R := by nlinarith
    have hball' : ball z' (2 * (R * ε ^ χ * k)) ⊆ ball (0 : ℂ) (ρ * R) := by
      rw [← Set.smul_set_subset_smul_set_iff₀ (ne_of_gt hc), smul_ball_pos hc, smul_ball_pos hc,
        smul_zero]
      convert hball using 2 <;> ring
    have hx' : x ∈ verticesMeeting (fun x => c⁻¹ • J x) (sphere z' (R * ε ^ χ * k)) := by
      rw [verticesMeeting_smul hc, smul_sphere_pos hc]
      exact hx
    have hmain := h2 m n k hz' hβ' hρ' hball' x hx'
    have hset : {ω | G.AnnularEvent (fun x => c⁻¹ • J x) z' (R * ε ^ χ * k) (G.vertexPath ω)} =
        {ω | G.AnnularEvent J (c • z') (c * (R * ε ^ χ * k)) (G.vertexPath ω)} := by
      ext ω
      exact annularEvent_smul_iff G J hc z' _ _
    rw [hset] at hmain
    exact hmain

/-- **Dilation covariance of the scaled-grid estimate event** (deterministic): shrinking all cells by `c > 0` and the
scale by `c` gives the same event. -/
theorem rawScaledGridControl_smul_iff {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) {c : ℝ}
    (hc : 0 < c) (R ε χ β q ρ p : ℝ) :
    RawScaledGridControl G (fun x => c⁻¹ • J x) R ε χ β q ρ p ↔
      RawScaledGridControl G J (c * R) ε χ β q ρ p := by
  refine ⟨rawScaledGridControl_of_smul G J hc, fun h => ?_⟩
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  have hJ : (fun x => c⁻¹⁻¹ • (fun x => c⁻¹ • J x) x) = J := by
    funext x
    simp only [inv_inv, smul_inv_smul₀ (ne_of_gt hc)]
  have h' : RawScaledGridControl G (fun x => c⁻¹⁻¹ • (fun x => c⁻¹ • J x) x) (c * R) ε χ β q ρ p := by
    rw [hJ]; exact h
  have := rawScaledGridControl_of_smul G (fun x => c⁻¹ • J x) hc' h'
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at this

/-! ### Transport along the edge-type identification -/

theorem rawScaledGridControl_cast_iff {E F : Type} (hEF : E = F) {G : LFMultigraph ℤ E}
    {G' : LFMultigraph ℤ F} (hG : cast (congrArg (LFMultigraph ℤ) hEF) G = G') (J : ℤ → Set ℂ)
    (R ε χ β q ρ p : ℝ) :
    RawScaledGridControl G J R ε χ β q ρ p ↔ RawScaledGridControl G' J R ε χ β q ρ p := by
  cases hEF
  change G = G' at hG
  subst G'
  rfl

theorem rawScaledGridControl_graph_congr {ε : ℝ} {Z₁ Z₂ : MatedCRT.Path2} (e : Z₁ = Z₂)
    (h₁ : MatedCRT.IsLocallyFinite ε Z₁) (h₂ : MatedCRT.IsLocallyFinite ε Z₂) (J : ℤ → Set ℂ)
    (R ε' χ β q ρ p : ℝ) :
    RawScaledGridControl (MatedCRT.graph ε Z₁ h₁) J R ε' χ β q ρ p ↔
      RawScaledGridControl (MatedCRT.graph ε Z₂ h₂) J R ε' χ β q ρ p := by
  subst e
  rfl

end MatedCRTHarmonic.CellScaling
