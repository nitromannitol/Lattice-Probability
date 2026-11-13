/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.Glue at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.UnorderedInterval

 








set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Strong

variable {X : Type*}

 
def seg (f : ℝ → X) (s s' : ℝ) : ℝ → X := fun u => f (s + u * (s' - s))

 
def glue4 (g₀ g₁ g₂ g₃ : ℝ → X) : ℝ → X := fun t =>
  if t ≤ 1 then g₀ t else if t ≤ 2 then g₁ (t - 1) else if t ≤ 3 then g₂ (t - 2) else g₃ (t - 3)

@[simp] theorem seg_zero (f : ℝ → X) (s s' : ℝ) : seg f s s' 0 = f s := by simp [seg]

@[simp] theorem seg_one (f : ℝ → X) (s s' : ℝ) : seg f s s' 1 = f s' := by simp [seg]

theorem seg_param_mem {a b s s' u : ℝ} (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b)
    (hu : u ∈ Icc (0 : ℝ) 1) : s + u * (s' - s) ∈ Icc a b := by
  obtain ⟨hu0, hu1⟩ := hu
  constructor <;> nlinarith [hs.1, hs.2, hs'.1, hs'.2, mul_nonneg hu0 (sub_nonneg.2 hu1)]

theorem mapsTo_seg {f : ℝ → X} {a b s s' : ℝ} {S : Set X} (hf : MapsTo f (Icc a b) S)
    (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) : MapsTo (seg f s s') (Icc 0 1) S :=
  fun _ hu => hf (seg_param_mem hs hs' hu)

theorem continuousOn_seg [TopologicalSpace X] {f : ℝ → X} {a b s s' : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) :
    ContinuousOn (seg f s s') (Icc 0 1) :=
  hf.comp (by fun_prop) fun _ hu => seg_param_mem hs hs' hu

theorem eVariationOn_seg_le [PseudoEMetricSpace X] (f : ℝ → X) {a b s s' : ℝ}
    (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) :
    eVariationOn (seg f s s') (Icc 0 1) ≤ eVariationOn f (Icc a b) := by
  have hmaps : MapsTo (fun u : ℝ => s + u * (s' - s)) (Icc 0 1) (Icc a b) :=
    fun _ hu => seg_param_mem hs hs' hu
  rcases le_total s s' with h | h
  · exact eVariationOn.comp_le_of_monotoneOn f _
      (fun x _ y _ hxy => by nlinarith [sub_nonneg.2 h]) hmaps
  · exact eVariationOn.comp_le_of_antitoneOn f _
      (fun x _ y _ hxy => by nlinarith [sub_nonneg.2 h]) hmaps

section Glue

variable (g₀ g₁ g₂ g₃ : ℝ → X)

theorem glue4_eqOn₀ : EqOn (glue4 g₀ g₁ g₂ g₃) g₀ (Icc 0 1) := fun t ht => by
  simp [glue4, ht.2]

theorem glue4_eqOn₁ (h₀₁ : g₀ 1 = g₁ 0) :
    EqOn (glue4 g₀ g₁ g₂ g₃) (fun t => g₁ (t - 1)) (Icc 1 2) := fun t ht => by
  by_cases h1 : t ≤ 1
  · have : t = 1 := le_antisymm h1 ht.1
    subst this; simp [glue4, h₀₁]
  · simp [glue4, h1, ht.2]

theorem glue4_eqOn₂ (h₁₂ : g₁ 1 = g₂ 0) :
    EqOn (glue4 g₀ g₁ g₂ g₃) (fun t => g₂ (t - 2)) (Icc 2 3) := fun t ht => by
  have h1 : ¬ t ≤ 1 := by linarith [ht.1]
  by_cases h2 : t ≤ 2
  · have : t = 2 := le_antisymm h2 ht.1
    subst this; norm_num [glue4, h₁₂]
  · simp [glue4, h1, h2, ht.2]

theorem glue4_eqOn₃ (h₂₃ : g₂ 1 = g₃ 0) :
    EqOn (glue4 g₀ g₁ g₂ g₃) (fun t => g₃ (t - 3)) (Icc 3 4) := fun t ht => by
  have h1 : ¬ t ≤ 1 := by linarith [ht.1]
  have h2 : ¬ t ≤ 2 := by linarith [ht.1]
  by_cases h3 : t ≤ 3
  · have : t = 3 := le_antisymm h3 ht.1
    subst this; norm_num [glue4, h₂₃]
  · simp [glue4, h1, h2, h3]

theorem Icc_zero_four : Icc (0 : ℝ) 4 = ((Icc 0 1 ∪ Icc 1 2) ∪ Icc 2 3) ∪ Icc 3 4 := by
  rw [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num),
    Icc_union_Icc_eq_Icc (by norm_num) (by norm_num),
    Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

theorem shift_continuousOn [TopologicalSpace X] {g : ℝ → X} (hg : ContinuousOn g (Icc 0 1))
    (k : ℝ) : ContinuousOn (fun t => g (t - k)) (Icc k (k + 1)) :=
  hg.comp (by fun_prop) fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem continuousOn_glue4 [TopologicalSpace X] (h₀ : ContinuousOn g₀ (Icc 0 1))
    (h₁ : ContinuousOn g₁ (Icc 0 1)) (h₂ : ContinuousOn g₂ (Icc 0 1))
    (h₃ : ContinuousOn g₃ (Icc 0 1)) (h₀₁ : g₀ 1 = g₁ 0) (h₁₂ : g₁ 1 = g₂ 0)
    (h₂₃ : g₂ 1 = g₃ 0) : ContinuousOn (glue4 g₀ g₁ g₂ g₃) (Icc 0 4) := by
  have c₀ := h₀.congr (glue4_eqOn₀ g₀ g₁ g₂ g₃)
  have s₁ : ContinuousOn (fun t => g₁ (t - 1)) (Icc 1 2) := by
    have := shift_continuousOn h₁ 1; norm_num at this; exact this
  have s₂ : ContinuousOn (fun t => g₂ (t - 2)) (Icc 2 3) := by
    have := shift_continuousOn h₂ 2; norm_num at this; exact this
  have s₃ : ContinuousOn (fun t => g₃ (t - 3)) (Icc 3 4) := by
    have := shift_continuousOn h₃ 3; norm_num at this; exact this
  have c₁ := s₁.congr (glue4_eqOn₁ g₀ g₁ g₂ g₃ h₀₁)
  have c₂ := s₂.congr (glue4_eqOn₂ g₀ g₁ g₂ g₃ h₁₂)
  have c₃ := s₃.congr (glue4_eqOn₃ g₀ g₁ g₂ g₃ h₂₃)
  rw [Icc_zero_four]
  exact (((c₀.union_of_isClosed c₁ isClosed_Icc isClosed_Icc).union_of_isClosed c₂
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc).union_of_isClosed c₃
    ((isClosed_Icc.union isClosed_Icc).union isClosed_Icc) isClosed_Icc)

theorem mapsTo_glue4 {S : Set X} (h₀ : MapsTo g₀ (Icc 0 1) S) (h₁ : MapsTo g₁ (Icc 0 1) S)
    (h₂ : MapsTo g₂ (Icc 0 1) S) (h₃ : MapsTo g₃ (Icc 0 1) S) :
    MapsTo (glue4 g₀ g₁ g₂ g₃) (Icc 0 4) S := by
  intro t ht
  unfold glue4
  split_ifs with a b c
  · exact h₀ ⟨ht.1, a⟩
  · exact h₁ ⟨by linarith, by linarith⟩
  · exact h₂ ⟨by linarith, by linarith⟩
  · exact h₃ ⟨by linarith, by linarith [ht.2]⟩

theorem eVariationOn_shift [PseudoEMetricSpace X] (g : ℝ → X) (k : ℝ) :
    eVariationOn (fun t => g (t - k)) (Icc k (k + 1)) = eVariationOn g (Icc 0 1) := by
  have := eVariationOn.comp_eq_of_monotoneOn g (fun t : ℝ => t - k)
    (t := Icc k (k + 1)) (fun x _ y _ hxy => by linarith)
  rw [image_sub_const_Icc, sub_self, add_sub_cancel_left] at this
  exact this

theorem eVariationOn_glue4 [PseudoEMetricSpace X] (h₀₁ : g₀ 1 = g₁ 0) (h₁₂ : g₁ 1 = g₂ 0)
    (h₂₃ : g₂ 1 = g₃ 0) :
    eVariationOn (glue4 g₀ g₁ g₂ g₃) (Icc 0 4) =
      eVariationOn g₀ (Icc 0 1) + eVariationOn g₁ (Icc 0 1) + eVariationOn g₂ (Icc 0 1) +
        eVariationOn g₃ (Icc 0 1) := by
  set G := glue4 g₀ g₁ g₂ g₃
  have e := fun (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) =>
    eVariationOn.Icc_add_Icc G (s := univ) hab hbc (mem_univ b)
  simp only [univ_inter] at e
  rw [← e 0 3 4 (by norm_num) (by norm_num), ← e 0 2 3 (by norm_num) (by norm_num),
    ← e 0 1 2 (by norm_num) (by norm_num)]
  rw [eVariationOn.eq_of_eqOn (glue4_eqOn₀ g₀ g₁ g₂ g₃),
    eVariationOn.eq_of_eqOn (glue4_eqOn₁ g₀ g₁ g₂ g₃ h₀₁),
    eVariationOn.eq_of_eqOn (glue4_eqOn₂ g₀ g₁ g₂ g₃ h₁₂),
    eVariationOn.eq_of_eqOn (glue4_eqOn₃ g₀ g₁ g₂ g₃ h₂₃)]
  have s1 := eVariationOn_shift g₁ 1
  have s2 := eVariationOn_shift g₂ 2
  have s3 := eVariationOn_shift g₃ 3
  norm_num at s1 s2 s3
  rw [s1, s2, s3]

end Glue

end SupercriticalLQGUniqueness.B2.Strong
