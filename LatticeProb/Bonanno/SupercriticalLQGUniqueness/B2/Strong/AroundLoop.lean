/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.AroundLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LogCross
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep
import LatticeProb.Bonanno.LQGMetric.Topo.SectorRect

 
















set_option autoImplicit false

noncomputable section

open Set Metric Complex

namespace SupercriticalLQGUniqueness.B2.Strong

 
structure Box where
  x₀ : ℝ
  x₁ : ℝ
  y₀ : ℝ
  y₁ : ℝ

namespace Box

 
def openSet (B : Box) : Set ℂ := {w | B.x₀ < w.re ∧ w.re < B.x₁ ∧ B.y₀ < w.im ∧ w.im < B.y₁}

 
def closedSet (B : Box) : Set ℂ := LQGMetric.RectCross.rect B.x₀ B.x₁ B.y₀ B.y₁

theorem closedSet_subset_openSet {K U : Box} (h₁ : U.x₀ < K.x₀) (h₂ : K.x₁ < U.x₁)
    (h₃ : U.y₀ < K.y₀) (h₄ : K.y₁ < U.y₁) : K.closedSet ⊆ U.openSet := by
  rintro w ⟨⟨a, b⟩, ⟨c, d⟩⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Box

 
def polarOpen (c : ℂ) (B : Box) : Set ℂ := expChart c '' B.openSet

 
def polarClosed (c : ℂ) (B : Box) : Set ℂ := expChart c '' B.closedSet

 
def PathIn (c : ℂ) (U K₁ K₂ : Box) (f : ℝ → ℂ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn f (Icc a b) ∧ MapsTo f (Icc a b) (polarOpen c U) ∧
    f a ∈ polarClosed c K₁ ∧ f b ∈ polarClosed c K₂

theorem blog_of_mem_openSet {c : ℂ} {θ : ℝ} {U : Box} (hU₀ : θ - Real.pi ≤ U.y₀)
    (hU₁ : U.y₁ ≤ θ + Real.pi) {w : ℂ} (hw : w ∈ U.openSet) :
    blog c θ (expChart c w) = w :=
  blog_expChart c w θ (by linarith [hw.2.2.1]) (by linarith [hw.2.2.2])

 
theorem PathIn.lift {c : ℂ} {θ : ℝ} {U K₁ K₂ : Box} {f : ℝ → ℂ} {a b : ℝ}
    (hP : PathIn c U K₁ K₂ f a b) (hU₀ : θ - Real.pi ≤ U.y₀) (hU₁ : U.y₁ ≤ θ + Real.pi)
    (hK₁ : K₁.closedSet ⊆ U.openSet) (hK₂ : K₂.closedSet ⊆ U.openSet) :
    ContinuousOn (fun t => blog c θ (f t)) (Icc a b) ∧
      (∀ t ∈ Icc a b, blog c θ (f t) ∈ U.openSet ∧ f t = expChart c (blog c θ (f t))) ∧
      blog c θ (f a) ∈ K₁.closedSet ∧ blog c θ (f b) ∈ K₂.closedSet := by
  obtain ⟨hab, hc, hmaps, ha, hb⟩ := hP
  refine ⟨continuousOn_blog_comp c θ hc fun t ht => ?_, fun t ht => ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hfw⟩ := hmaps ht
    exact ⟨w, by linarith [hw.2.2.1], by linarith [hw.2.2.2], hfw.symm⟩
  · obtain ⟨w, hw, hfw⟩ := hmaps ht
    rw [← hfw, blog_of_mem_openSet hU₀ hU₁ hw]
    exact ⟨hw, rfl⟩
  · obtain ⟨w, hw, hfw⟩ := ha
    rw [← hfw, blog_of_mem_openSet hU₀ hU₁ (hK₁ hw)]
    exact hw
  · obtain ⟨w, hw, hfw⟩ := hb
    rw [← hfw, blog_of_mem_openSet hU₀ hU₁ (hK₂ hw)]
    exact hw

 

 
def wd : ℝ := Real.pi / 8

theorem wd_pos : 0 < wd := by unfold wd; linarith [Real.pi_pos]

 
def boxR (L Δ θ : ℝ) : Box := ⟨L + 2 * Δ, L + 14 * Δ, θ - wd, θ + wd⟩
 
def segR (θ x : ℝ) : Box := ⟨x, x, θ - wd / 2, θ + wd / 2⟩
 
def boxA (L Δ y₀ y₁ : ℝ) : Box := ⟨L + 6 * Δ, L + 10 * Δ, y₀, y₁⟩
 
def segA (L Δ y : ℝ) : Box := ⟨L + 7 * Δ, L + 9 * Δ, y, y⟩

 
def cfgU (L Δ : ℝ) : Fin 4 → Box
  | 0 => boxR L Δ 0
  | 1 => boxA L Δ (-(3 * wd)) (Real.pi + 3 * wd)
  | 2 => boxR L Δ Real.pi
  | 3 => boxA L Δ (Real.pi - 3 * wd) (2 * Real.pi + 3 * wd)

def cfgK₁ (L Δ : ℝ) : Fin 4 → Box
  | 0 => segR 0 (L + 4 * Δ)
  | 1 => segA L Δ (-(2 * wd))
  | 2 => segR Real.pi (L + 4 * Δ)
  | 3 => segA L Δ (Real.pi - 2 * wd)

def cfgK₂ (L Δ : ℝ) : Fin 4 → Box
  | 0 => segR 0 (L + 12 * Δ)
  | 1 => segA L Δ (Real.pi + 2 * wd)
  | 2 => segR Real.pi (L + 12 * Δ)
  | 3 => segA L Δ (2 * Real.pi + 2 * wd)

 
def cfgθ : Fin 4 → ℝ
  | 0 => 0
  | 1 => Real.pi / 2
  | 2 => Real.pi
  | 3 => 3 * Real.pi / 2

theorem cfgK₁_subset (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    (cfgK₁ L Δ k).closedSet ⊆ (cfgU L Δ k).openSet := by
  have := wd_pos
  have h8 : 8 * wd = Real.pi := by unfold wd; ring
  fin_cases k <;>
    exact Box.closedSet_subset_openSet (by simp [cfgK₁, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₁, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₁, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₁, cfgU, boxR, segR, boxA, segA]; linarith)

theorem cfgK₂_subset (L Δ : ℝ) (hΔ : 0 < Δ) (k : Fin 4) :
    (cfgK₂ L Δ k).closedSet ⊆ (cfgU L Δ k).openSet := by
  have := wd_pos
  have h8 : 8 * wd = Real.pi := by unfold wd; ring
  fin_cases k <;>
    exact Box.closedSet_subset_openSet (by simp [cfgK₂, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₂, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₂, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₂, cfgU, boxR, segR, boxA, segA]; linarith)

theorem cfgU_window (L Δ : ℝ) (k : Fin 4) :
    cfgθ k - Real.pi ≤ (cfgU L Δ k).y₀ ∧ (cfgU L Δ k).y₁ ≤ cfgθ k + Real.pi := by
  have := Real.pi_pos
  fin_cases k <;> refine ⟨?_, ?_⟩ <;> simp [cfgθ, cfgU, boxR, boxA, wd] <;> linarith

 

theorem norm_sub_of_mem_polarOpen {c : ℂ} {L Δ : ℝ} (hΔ : 0 < Δ) (k : Fin 4) {z : ℂ}
    (hz : z ∈ polarOpen c (cfgU L Δ k)) :
    Real.exp L < ‖z - c‖ ∧ ‖z - c‖ < Real.exp (L + 16 * Δ) := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hre : L < w.re ∧ w.re < L + 16 * Δ := by
    obtain ⟨h1, h2, -, -⟩ := hw
    fin_cases k <;> simp [cfgU, boxR, boxA] at h1 h2 <;> constructor <;> linarith
  rw [expChart, add_sub_cancel_left, Complex.norm_exp]
  exact ⟨Real.exp_lt_exp.2 hre.1, Real.exp_lt_exp.2 hre.2⟩

theorem glue4_congr {X : Type*} {g₀ g₁ g₂ g₃ h₀ h₁ h₂ h₃ : ℝ → X}
    (e₀ : EqOn g₀ h₀ (Icc 0 1)) (e₁ : EqOn g₁ h₁ (Icc 0 1)) (e₂ : EqOn g₂ h₂ (Icc 0 1))
    (e₃ : EqOn g₃ h₃ (Icc 0 1)) : EqOn (glue4 g₀ g₁ g₂ g₃) (glue4 h₀ h₁ h₂ h₃) (Icc 0 4) := by
  intro t ht
  unfold glue4
  split_ifs with a b c
  · exact e₀ ⟨ht.1, a⟩
  · exact e₁ ⟨by linarith, by linarith⟩
  · exact e₂ ⟨by linarith, by linarith⟩
  · exact e₃ ⟨by linarith, by linarith [ht.2]⟩

theorem seg_congr {X : Type*} {f g : ℝ → X} {a b s s' : ℝ} (e : EqOn f g (Icc a b))
    (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) : EqOn (seg f s s') (seg g s s') (Icc 0 1) :=
  fun _ hu => e (seg_param_mem hs hs' hu)

 


theorem exists_around_loop (c : ℂ) {L Δ : ℝ} (hΔ : 0 < Δ) {f₀ f₁ f₂ f₃ : ℝ → ℂ}
    {a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hf₀ : PathIn c (cfgU L Δ 0) (cfgK₁ L Δ 0) (cfgK₂ L Δ 0) f₀ a₀ b₀)
    (hf₁ : PathIn c (cfgU L Δ 1) (cfgK₁ L Δ 1) (cfgK₂ L Δ 1) f₁ a₁ b₁)
    (hf₂ : PathIn c (cfgU L Δ 2) (cfgK₁ L Δ 2) (cfgK₂ L Δ 2) f₂ a₂ b₂)
    (hf₃ : PathIn c (cfgU L Δ 3) (cfgK₁ L Δ 3) (cfgK₂ L Δ 3) f₃ a₃ b₃) :
    ∃ s₀ ∈ Icc a₀ b₀, ∃ s₀' ∈ Icc a₀ b₀, ∃ s₁ ∈ Icc a₁ b₁, ∃ s₁' ∈ Icc a₁ b₁,
      ∃ s₂ ∈ Icc a₂ b₂, ∃ s₂' ∈ Icc a₂ b₂, ∃ s₃ ∈ Icc a₃ b₃, ∃ s₃' ∈ Icc a₃ b₃,
      f₀ s₀' = f₁ s₁ ∧ f₁ s₁' = f₂ s₂ ∧ f₂ s₂' = f₃ s₃ ∧
      LQGMetric.Disconnects
        (glue4 (seg f₀ s₀ s₀') (seg f₁ s₁ s₁') (seg f₂ s₂ s₂') (seg f₃ s₃ s₃') '' Icc 0 4)
        (sphere c (Real.exp L)) (sphere c (Real.exp (L + 16 * Δ))) := by
  have hw := wd_pos
  have hpi := Real.pi_pos
  have hw8 : wd = Real.pi / 8 := rfl
  obtain ⟨c₀, e₀, a₀m, b₀m⟩ := hf₀.lift (θ := cfgθ 0) (cfgU_window L Δ 0).1
    (cfgU_window L Δ 0).2 (cfgK₁_subset L Δ hΔ 0) (cfgK₂_subset L Δ hΔ 0)
  obtain ⟨c₁, e₁, a₁m, b₁m⟩ := hf₁.lift (θ := cfgθ 1) (cfgU_window L Δ 1).1
    (cfgU_window L Δ 1).2 (cfgK₁_subset L Δ hΔ 1) (cfgK₂_subset L Δ hΔ 1)
  obtain ⟨c₂, e₂, a₂m, b₂m⟩ := hf₂.lift (θ := cfgθ 2) (cfgU_window L Δ 2).1
    (cfgU_window L Δ 2).2 (cfgK₁_subset L Δ hΔ 2) (cfgK₂_subset L Δ hΔ 2)
  obtain ⟨c₃, e₃, a₃m, b₃m⟩ := hf₃.lift (θ := cfgθ 3) (cfgU_window L Δ 3).1
    (cfgU_window L Δ 3).2 (cfgK₁_subset L Δ hΔ 3) (cfgK₂_subset L Δ hΔ 3)
  set ℓ₀ := fun t => blog c (cfgθ 0) (f₀ t)
  set ℓ₁ := fun t => blog c (cfgθ 1) (f₁ t)
  set ℓ₂ := fun t => blog c (cfgθ 2) (f₂ t)
  set ℓ₃ := fun t => blog c (cfgθ 3) (f₃ t)
  simp only [cfgU, cfgK₁, cfgK₂, boxR, boxA, segR, segA, Box.openSet, Box.closedSet,
    LQGMetric.RectCross.rect, mem_ofPred_eq, mem_Icc] at e₀ e₁ e₂ e₃ a₀m b₀m a₁m b₁m a₂m b₂m a₃m b₃m
  have hab₀ := hf₀.1
  have hab₁ := hf₁.1
  have hab₂ := hf₂.1
  have hab₃ := hf₃.1
  
  obtain ⟨σ₁, hσ₁, τ₁, hτ₁, m₁⟩ := crossings_meet (x₀ := L + 6 * Δ) (x₁ := L + 10 * Δ)
    (y₀ := -wd) (y₁ := wd) hab₀ hab₁ (by linarith) (by linarith) c₀ c₁
    (by linarith [a₀m.1.1]) (by linarith [b₀m.1.1])
    (fun t ht => ⟨by linarith [(e₀ t ht).1.2.2.1], by linarith [(e₀ t ht).1.2.2.2]⟩)
    (by linarith [a₁m.2.1]) (by linarith [b₁m.2.1])
    (fun t ht => ⟨(e₁ t ht).1.1.le, (e₁ t ht).1.2.1.le⟩)
  
  obtain ⟨σ₂, hσ₂, τ₂, hτ₂, m₂⟩ := crossings_meet (x₀ := L + 6 * Δ) (x₁ := L + 10 * Δ)
    (y₀ := Real.pi - wd) (y₁ := Real.pi + wd) hab₂ hab₁ (by linarith) (by linarith) c₂ c₁
    (by linarith [a₂m.1.1]) (by linarith [b₂m.1.1])
    (fun t ht => ⟨by linarith [(e₂ t ht).1.2.2.1], by linarith [(e₂ t ht).1.2.2.2]⟩)
    (by linarith [a₁m.2.1]) (by linarith [b₁m.2.1])
    (fun t ht => ⟨(e₁ t ht).1.1.le, (e₁ t ht).1.2.1.le⟩)
  
  obtain ⟨σ₃, hσ₃, τ₃, hτ₃, m₃⟩ := crossings_meet (x₀ := L + 6 * Δ) (x₁ := L + 10 * Δ)
    (y₀ := Real.pi - wd) (y₁ := Real.pi + wd) hab₂ hab₃ (by linarith) (by linarith) c₂ c₃
    (by linarith [a₂m.1.1]) (by linarith [b₂m.1.1])
    (fun t ht => ⟨by linarith [(e₂ t ht).1.2.2.1], by linarith [(e₂ t ht).1.2.2.2]⟩)
    (by linarith [a₃m.2.1]) (by linarith [b₃m.2.1])
    (fun t ht => ⟨(e₃ t ht).1.1.le, (e₃ t ht).1.2.1.le⟩)
  
  obtain ⟨σ₄, hσ₄, τ₄, hτ₄, m₄⟩ := crossings_meet (ℓ₁ := fun t => ℓ₀ t + 2 * Real.pi * I)
    (x₀ := L + 6 * Δ) (x₁ := L + 10 * Δ)
    (y₀ := 2 * Real.pi - wd) (y₁ := 2 * Real.pi + wd) hab₀ hab₃ (by linarith) (by linarith)
    (c₀.add continuousOn_const) c₃
    (by simp; linarith [a₀m.1.1]) (by simp; linarith [b₀m.1.1])
    (fun t ht => ⟨by simp; linarith [(e₀ t ht).1.2.2.1], by simp; linarith [(e₀ t ht).1.2.2.2]⟩)
    (by linarith [a₃m.2.1]) (by linarith [b₃m.2.1])
    (fun t ht => ⟨(e₃ t ht).1.1.le, (e₃ t ht).1.2.1.le⟩)
  
  have z₁ : f₀ σ₁ = f₁ τ₁ := by rw [(e₀ σ₁ hσ₁).2, (e₁ τ₁ hτ₁).2]; exact congrArg _ m₁
  have z₂ : f₁ τ₂ = f₂ σ₂ := by rw [(e₂ σ₂ hσ₂).2, (e₁ τ₂ hτ₂).2]; exact congrArg _ m₂.symm
  have z₃ : f₂ σ₃ = f₃ τ₃ := by rw [(e₂ σ₃ hσ₃).2, (e₃ τ₃ hτ₃).2]; exact congrArg _ m₃
  refine ⟨σ₄, hσ₄, σ₁, hσ₁, τ₁, hτ₁, τ₂, hτ₂, σ₂, hσ₂, σ₃, hσ₃, τ₃, hτ₃, τ₄, hτ₄,
    z₁, z₂, z₃, ?_⟩
  set P := glue4 (seg f₀ σ₄ σ₁) (seg f₁ τ₁ τ₂) (seg f₂ σ₂ σ₃) (seg f₃ τ₃ τ₄)
  set Λ := glue4 (seg ℓ₀ σ₄ σ₁) (seg ℓ₁ τ₁ τ₂) (seg ℓ₂ σ₂ σ₃) (seg ℓ₃ τ₃ τ₄)
  have hPc : ContinuousOn P (Icc 0 4) :=
    continuousOn_glue4 _ _ _ _ (continuousOn_seg hf₀.2.1 hσ₄ hσ₁)
      (continuousOn_seg hf₁.2.1 hτ₁ hτ₂) (continuousOn_seg hf₂.2.1 hσ₂ hσ₃)
      (continuousOn_seg hf₃.2.1 hτ₃ hτ₄) (by simpa using z₁) (by simpa using z₂)
      (by simpa using z₃)
  have hΛc : ContinuousOn Λ (Icc 0 4) :=
    continuousOn_glue4 _ _ _ _ (continuousOn_seg c₀ hσ₄ hσ₁)
      (continuousOn_seg c₁ hτ₁ hτ₂) (continuousOn_seg c₂ hσ₂ hσ₃)
      (continuousOn_seg c₃ hτ₃ hτ₄) (by simpa using m₁) (by simpa using m₂.symm)
      (by simpa using m₃)
  have hexp : ∀ t ∈ Icc (0 : ℝ) 4, P t = c + Complex.exp (Λ t) := by
    have hE : EqOn P (glue4 (seg (fun t => expChart c (ℓ₀ t)) σ₄ σ₁)
        (seg (fun t => expChart c (ℓ₁ t)) τ₁ τ₂) (seg (fun t => expChart c (ℓ₂ t)) σ₂ σ₃)
        (seg (fun t => expChart c (ℓ₃ t)) τ₃ τ₄)) (Icc 0 4) :=
      glue4_congr (seg_congr (fun t ht => (e₀ t ht).2) hσ₄ hσ₁)
        (seg_congr (fun t ht => (e₁ t ht).2) hτ₁ hτ₂)
        (seg_congr (fun t ht => (e₂ t ht).2) hσ₂ hσ₃)
        (seg_congr (fun t ht => (e₃ t ht).2) hτ₃ hτ₄)
    intro t ht
    rw [hE ht]
    simp only [glue4, Λ, seg, expChart]
    split_ifs <;> rfl
  have hend : Λ 4 = Λ 0 + 2 * Real.pi * I := by
    have h4 : Λ 4 = ℓ₃ τ₄ := by simp only [Λ, glue4, seg]; norm_num
    have h0 : Λ 0 = ℓ₀ σ₄ := by simp only [Λ, glue4, seg]; norm_num
    rw [h4, h0]
    exact m₄.symm
  have hmapsP : MapsTo P (Icc 0 4) {z | Real.exp L < ‖z - c‖ ∧ ‖z - c‖ < Real.exp (L + 16 * Δ)} :=
    mapsTo_glue4 _ _ _ _
      (mapsTo_seg (fun t ht => norm_sub_of_mem_polarOpen hΔ 0 (hf₀.2.2.1 ht)) hσ₄ hσ₁)
      (mapsTo_seg (fun t ht => norm_sub_of_mem_polarOpen hΔ 1 (hf₁.2.2.1 ht)) hτ₁ hτ₂)
      (mapsTo_seg (fun t ht => norm_sub_of_mem_polarOpen hΔ 2 (hf₂.2.2.1 ht)) hσ₂ hσ₃)
      (mapsTo_seg (fun t ht => norm_sub_of_mem_polarOpen hΔ 3 (hf₃.2.2.1 ht)) hτ₃ hτ₄)
  exact disconnects_of_lift (by norm_num) hPc hΛc hexp hend (fun t ht => (hmapsP ht).1)
    (fun t ht => (hmapsP ht).2)

end SupercriticalLQGUniqueness.B2.Strong
