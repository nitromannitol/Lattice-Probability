/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.LogCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

 











set_option autoImplicit false

noncomputable section

open Set Complex

namespace SupercriticalLQGUniqueness.B2.Strong

 
def expChart (c w : ℂ) : ℂ := c + Complex.exp w

 
def blog (c : ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  Complex.log ((z - c) * Complex.exp (-((θ : ℂ) * I))) + (θ : ℂ) * I

theorem expChart_sub_mul (c w : ℂ) (θ : ℝ) :
    (expChart c w - c) * Complex.exp (-((θ : ℂ) * I)) = Complex.exp (w - (θ : ℂ) * I) := by
  rw [expChart, add_sub_cancel_left, sub_eq_add_neg, Complex.exp_add]

theorem im_sub_theta (w : ℂ) (θ : ℝ) : (w - (θ : ℂ) * I).im = w.im - θ := by
  simp

 
theorem blog_expChart (c w : ℂ) (θ : ℝ) (h₁ : θ - Real.pi < w.im) (h₂ : w.im < θ + Real.pi) :
    blog c θ (expChart c w) = w := by
  rw [blog, expChart_sub_mul, Complex.log_exp (by rw [im_sub_theta]; linarith)
    (by rw [im_sub_theta]; linarith)]
  ring

theorem exp_mem_slitPlane_of_abs_im_lt {v : ℂ} (h₁ : -Real.pi < v.im) (h₂ : v.im < Real.pi) :
    Complex.exp v ∈ slitPlane := by
  rw [Complex.exp_mem_slitPlane]
  have hmem : v.im ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := ⟨h₁, by linarith⟩
  rw [(toIocMod_eq_self Real.two_pi_pos).2 hmem]
  exact h₂.ne

 
theorem continuousAt_blog (c w : ℂ) (θ : ℝ) (h₁ : θ - Real.pi < w.im)
    (h₂ : w.im < θ + Real.pi) : ContinuousAt (blog c θ) (expChart c w) := by
  have hs : (expChart c w - c) * Complex.exp (-((θ : ℂ) * I)) ∈ slitPlane := by
    rw [expChart_sub_mul]
    exact exp_mem_slitPlane_of_abs_im_lt (by rw [im_sub_theta]; linarith)
      (by rw [im_sub_theta]; linarith)
  have hg : ContinuousAt (fun z : ℂ => (z - c) * Complex.exp (-((θ : ℂ) * I))) (expChart c w) := by
    fun_prop
  exact ((continuousAt_clog hs).comp (f := fun z : ℂ => (z - c) * Complex.exp (-((θ : ℂ) * I)))
    hg).add continuousAt_const

 

theorem continuousOn_blog_comp {f : ℝ → ℂ} {S : Set ℝ} (c : ℂ) (θ : ℝ)
    (hf : ContinuousOn f S)
    (hstrip : ∀ t ∈ S, ∃ w : ℂ, θ - Real.pi < w.im ∧ w.im < θ + Real.pi ∧ f t = expChart c w) :
    ContinuousOn (fun t => blog c θ (f t)) S := by
  intro t ht
  obtain ⟨w, h₁, h₂, hfw⟩ := hstrip t ht
  have := continuousAt_blog c w θ h₁ h₂
  rw [← hfw] at this
  exact this.comp_continuousWithinAt (hf t ht)

theorem affine_mem_Icc {s t u : ℝ} (hst : s ≤ t) (hu : u ∈ Icc (0 : ℝ) 1) :
    s + u * (t - s) ∈ Icc s t := by
  constructor <;> nlinarith [hu.1, hu.2]

theorem affine_rev_mem_Icc {s t u : ℝ} (hst : s ≤ t) (hu : u ∈ Icc (0 : ℝ) 1) :
    t + u * (s - t) ∈ Icc s t := by
  constructor <;> nlinarith [hu.1, hu.2]

 


theorem crossings_meet {ℓ₁ ℓ₂ : ℝ → ℂ} {a₁ b₁ a₂ b₂ x₀ x₁ y₀ y₁ : ℝ}
    (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂) (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h₁ : ContinuousOn ℓ₁ (Icc a₁ b₁)) (h₂ : ContinuousOn ℓ₂ (Icc a₂ b₂))
    (h₁a : (ℓ₁ a₁).re ≤ x₀) (h₁b : x₁ ≤ (ℓ₁ b₁).re)
    (h₁y : ∀ t ∈ Icc a₁ b₁, (ℓ₁ t).im ∈ Icc y₀ y₁)
    (h₂a : (ℓ₂ a₂).im ≤ y₀) (h₂b : y₁ ≤ (ℓ₂ b₂).im)
    (h₂x : ∀ t ∈ Icc a₂ b₂, (ℓ₂ t).re ∈ Icc x₀ x₁) :
    ∃ s ∈ Icc a₁ b₁, ∃ t ∈ Icc a₂ b₂, ℓ₁ s = ℓ₂ t := by
  obtain ⟨s₁, t₁, hs₁, hst₁, ht₁, hres, hret, hre⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (f := fun u => (ℓ₁ u).re) hab₁
      (Complex.continuous_re.comp_continuousOn h₁) hx h₁a h₁b
  obtain ⟨s₂, t₂, hs₂, hst₂, ht₂, hims, himt, him⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (f := fun u => (ℓ₂ u).im) hab₂
      (Complex.continuous_im.comp_continuousOn h₂) hy h₂a h₂b
  have hsub₁ : Icc s₁ t₁ ⊆ Icc a₁ b₁ := Icc_subset_Icc hs₁ ht₁
  have hsub₂ : Icc s₂ t₂ ⊆ Icc a₂ b₂ := Icc_subset_Icc hs₂ ht₂
  set γ : ℝ → ℂ := fun u => ℓ₁ (s₁ + u * (t₁ - s₁)) with hγ
  set δ : ℝ → ℂ := fun u => ℓ₂ (t₂ + u * (s₂ - t₂)) with hδ
  have hγc : ContinuousOn γ (Icc 0 1) :=
    h₁.comp (by fun_prop) fun u hu => hsub₁ (affine_mem_Icc hst₁ hu)
  have hδc : ContinuousOn δ (Icc 0 1) :=
    h₂.comp (by fun_prop) fun u hu => hsub₂ (affine_rev_mem_Icc hst₂ hu)
  have hγm : MapsTo γ (Icc 0 1) (LQGMetric.RectCross.rect x₀ x₁ y₀ y₁) := fun u hu =>
    ⟨hre _ (affine_mem_Icc hst₁ hu), h₁y _ (hsub₁ (affine_mem_Icc hst₁ hu))⟩
  have hδm : MapsTo δ (Icc 0 1) (LQGMetric.RectCross.rect x₀ x₁ y₀ y₁) := fun u hu =>
    ⟨h₂x _ (hsub₂ (affine_rev_mem_Icc hst₂ hu)), him _ (affine_rev_mem_Icc hst₂ hu)⟩
  obtain ⟨u, hu, v, hv, huv⟩ := LQGMetric.RectMeet.rect_crossings_meet x₀ x₁ y₀ y₁ γ δ hγc hδc
    hγm hδm (by simp [hγ, hres]) (by simp [hγ, hret]) (by simp [hδ, himt])
    (by simp [hδ, hims])
  exact ⟨_, hsub₁ (affine_mem_Icc hst₁ hu), _, hsub₂ (affine_rev_mem_Icc hst₂ hv), huv⟩

end SupercriticalLQGUniqueness.B2.Strong
