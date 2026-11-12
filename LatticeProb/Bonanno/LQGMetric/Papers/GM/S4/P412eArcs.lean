/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eArcs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

/-!
# Splitting a Jordan curve at two points (input of `theta_bounded` for GM L4.13′)

P2-CROSSCUT "Still needed" item 1: a Jordan curve `Γ = γ(∂𝔻)` (`JordanMap.IsJordanCurve`) and
`p ≠ q ∈ Γ` give compact arcs `A, B ⊆ Γ` with `A ∪ B = Γ`, `A ∩ B = {p, q}`; their open parts
`A°, B°` are preconnected, miss `p, q`, and have `p, q` in their closures. On the circle:
`c(t) = e^{2πit}`, `p = γ(c t₁)`, `q = γ(c t₂)`, `t₁ < t₂ < t₁ + 1`, `A = γ(c[t₁,t₂])`,
`B = γ(c[t₂,t₁+1])`. Own elementary argument (standard).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter Complex

namespace LQGMetric.GM

/-- `c(t) = e^{2πit}` -/
def p412eC (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)

theorem p412eC_continuous : Continuous p412eC := by unfold p412eC; fun_prop

theorem p412eC_mem (t : ℝ) : p412eC t ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, p412eC, Complex.norm_exp_ofReal_mul_I]

theorem p412eC_eq_iff {s t : ℝ} : p412eC s = p412eC t ↔ ∃ n : ℤ, s = t + n := by
  unfold p412eC
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : ((s : ℂ) - t - n) * (2 * Real.pi * I) = 0 := by push_cast at hn; linear_combination hn
    rcases mul_eq_zero.1 h2 with h | h
    · have : ((s - t - n : ℝ) : ℂ) = 0 := by push_cast; exact h
      have := Complex.ofReal_eq_zero.1 this; linarith
    · exfalso; simp [hpi, I_ne_zero] at h
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem p412eC_add_int (t : ℝ) (n : ℤ) : p412eC (t + n) = p412eC t :=
  p412eC_eq_iff.2 ⟨n, rfl⟩

theorem p412eC_surj {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) : ∃ t, p412eC t = w := by
  have hn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
  refine ⟨arg w / (2 * Real.pi), ?_⟩
  have he : 2 * Real.pi * (arg w / (2 * Real.pi)) = arg w := by
    field_simp
  rw [p412eC, he]
  have h := norm_mul_exp_arg_mul_I w
  rwa [hn, Complex.ofReal_one, one_mul] at h

theorem p412eC_image_Icc (t₁ : ℝ) : p412eC '' Icc t₁ (t₁ + 1) = sphere (0 : ℂ) 1 := by
  refine subset_antisymm (by rintro _ ⟨t, -, rfl⟩; exact p412eC_mem t) fun w hw => ?_
  obtain ⟨t, rfl⟩ := p412eC_surj hw
  have h := toIcoMod_mem_Ico one_pos t₁ t
  refine ⟨toIcoMod one_pos t₁ t, ⟨h.1, h.2.le⟩, p412eC_eq_iff.2 ⟨-toIcoDiv one_pos t₁ t, ?_⟩⟩
  rw [toIcoMod]; push_cast; ring

/-- two parameters in a half-open period with equal `c`-values coincide -/
theorem p412eC_inj {t₁ s s' : ℝ} (hs : s ∈ Icc t₁ (t₁ + 1)) (hs' : s' ∈ Icc t₁ (t₁ + 1))
    (h : p412eC s = p412eC s') : s = s' ∨ (s = t₁ ∧ s' = t₁ + 1) ∨ (s = t₁ + 1 ∧ s' = t₁) := by
  obtain ⟨n, hn⟩ := p412eC_eq_iff.1 h
  have h1 : (n : ℝ) ≤ 1 := by linarith [hs.2, hs'.1]
  have h2 : (-1 : ℝ) ≤ n := by linarith [hs.1, hs'.2]
  have h1' : n ≤ 1 := by exact_mod_cast h1
  have h2' : -1 ≤ n := by exact_mod_cast h2
  interval_cases n
  · right; left; push_cast at hn; constructor <;> linarith [hs.2, hs'.1, hs.1, hs'.2]
  · left; push_cast at hn; linarith
  · right; right; push_cast at hn; constructor <;> linarith [hs.2, hs'.1, hs.1, hs'.2]

/-- **Splitting a Jordan curve at `p ≠ q`** -/
theorem p412e_split {γ : ℂ → ℂ} (hγc : ContinuousOn γ (sphere 0 1)) (hγi : InjOn γ (sphere 0 1))
    {p q : ℂ} (hp : p ∈ γ '' sphere 0 1) (hq : q ∈ γ '' sphere 0 1) (hpq : p ≠ q) :
    ∃ A B A₀ B₀ : Set ℂ, IsCompact A ∧ IsCompact B ∧ A ∪ B = γ '' sphere 0 1 ∧ A ∩ B = {p, q} ∧
      A₀ ⊆ A ∧ B₀ ⊆ B ∧ A = A₀ ∪ {p, q} ∧ B = B₀ ∪ {p, q} ∧ p ∉ A₀ ∧ q ∉ A₀ ∧ p ∉ B₀ ∧
      q ∉ B₀ ∧ IsPreconnected A₀ ∧ IsPreconnected B₀ ∧ p ∈ closure A₀ ∧ q ∈ closure A₀ ∧
      p ∈ closure B₀ ∧ q ∈ closure B₀ := by
  obtain ⟨ζ₁, hζ₁, rfl⟩ := hp
  obtain ⟨ζ₂, hζ₂, rfl⟩ := hq
  obtain ⟨t₁, rfl⟩ := p412eC_surj hζ₁
  obtain ⟨t₂', rfl⟩ := p412eC_surj hζ₂
  set t₂ := toIcoMod one_pos t₁ t₂'
  have ht₂ := toIcoMod_mem_Ico one_pos t₁ t₂'
  have hc₂ : p412eC t₂ = p412eC t₂' := p412eC_eq_iff.2 ⟨-toIcoDiv one_pos t₁ t₂', by
    simp only [t₂, toIcoMod]; push_cast; ring⟩
  rw [← hc₂] at hpq ⊢
  have h12 : t₁ < t₂ := lt_of_le_of_ne ht₂.1 (fun h => hpq (by rw [h]))
  have h21 : t₂ < t₁ + 1 := ht₂.2
  have hS : ∀ s, p412eC s ∈ sphere (0 : ℂ) 1 := p412eC_mem
  have hc1 : p412eC (t₁ + 1) = p412eC t₁ := by
    have := p412eC_add_int t₁ 1; push_cast at this; exact this
  set A' := p412eC '' Icc t₁ t₂
  set B' := p412eC '' Icc t₂ (t₁ + 1)
  have hA'S : A' ⊆ sphere 0 1 := by rintro _ ⟨s, -, rfl⟩; exact hS s
  have hB'S : B' ⊆ sphere 0 1 := by rintro _ ⟨s, -, rfl⟩; exact hS s
  have hγc' : Continuous p412eC := p412eC_continuous
  -- membership facts of `γ ∘ c` for parameters in one period
  have hval : ∀ s ∈ Icc t₁ (t₁ + 1), ∀ s' ∈ Icc t₁ (t₁ + 1),
      γ (p412eC s) = γ (p412eC s') → s = s' ∨ (s = t₁ ∧ s' = t₁ + 1) ∨ (s = t₁ + 1 ∧ s' = t₁) :=
    fun s hs s' hs' h => p412eC_inj hs hs' (hγi (hS s) (hS s') h)
  -- the composite `γ ∘ c` on one period
  have hgc : ContinuousOn (γ ∘ p412eC) (Icc t₁ (t₁ + 1)) :=
    hγc.comp hγc'.continuousOn fun s _ => hS s
  have hIcc : ∀ {a b : ℝ}, t₁ ≤ a → b ≤ t₁ + 1 → ∀ s ∈ Icc a b, s ∈ Icc t₁ (t₁ + 1) :=
    fun ha hb s hs => ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hsplit : ∀ {a b : ℝ}, a ≤ b → γ '' (p412eC '' Icc a b) =
      γ '' (p412eC '' Ioo a b) ∪ {γ (p412eC a), γ (p412eC b)} := by
    intro a b hab
    ext w
    simp only [mem_image, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      rcases eq_or_lt_of_le hs.1 with h | h
      · right; left; rw [h]
      rcases eq_or_lt_of_le hs.2 with h' | h'
      · right; right; rw [h']
      · left; exact ⟨_, ⟨s, ⟨h, h'⟩, rfl⟩, rfl⟩
    · rintro (⟨_, ⟨s, hs, rfl⟩, rfl⟩ | rfl | rfl)
      · exact ⟨_, ⟨s, Ioo_subset_Icc_self hs, rfl⟩, rfl⟩
      · exact ⟨_, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, rfl⟩
      · exact ⟨_, ⟨b, ⟨hab, le_rfl⟩, rfl⟩, rfl⟩
  have hnot : ∀ {a b : ℝ}, t₁ ≤ a → b ≤ t₁ + 1 → ∀ r, (r = t₁ ∨ r = t₂) → r ∉ Ioo a b →
      γ (p412eC r) ∉ γ '' (p412eC '' Ioo a b) := by
    rintro a b ha hb r hr hrab ⟨_, ⟨s, hs, rfl⟩, hsr⟩
    have hr' : r ∈ Icc t₁ (t₁ + 1) := by
      rcases hr with rfl | rfl
      · exact ⟨le_rfl, by linarith⟩
      · exact ⟨h12.le, h21.le⟩
    rcases hval s (hIcc ha hb s (Ioo_subset_Icc_self hs)) r hr' hsr with h | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hrab (h ▸ hs)
    · linarith [hs.1, hs.2]
    · linarith [hs.1, hs.2]
  have hcl : ∀ {a b : ℝ}, t₁ ≤ a → b ≤ t₁ + 1 → a < b →
      γ (p412eC a) ∈ closure (γ '' (p412eC '' Ioo a b)) ∧
        γ (p412eC b) ∈ closure (γ '' (p412eC '' Ioo a b)) := by
    intro a b ha hb hab
    have hg : ContinuousOn (γ ∘ p412eC) (Icc a b) := hgc.mono fun s hs => hIcc ha hb s hs
    rw [image_image]
    have hm : Icc a b ⊆ closure (Ioo a b) := by rw [closure_Ioo hab.ne]
    exact ⟨(hg a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self |>.mem_closure_image (hm ⟨le_rfl, hab.le⟩),
      (hg b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self |>.mem_closure_image (hm ⟨hab.le, le_rfl⟩)⟩
  have hpre : ∀ a b : ℝ, IsPreconnected (γ '' (p412eC '' Ioo a b)) := fun a b =>
    (isPreconnected_Ioo.image _ hγc'.continuousOn).image γ (hγc.mono fun _ ⟨s, _, h⟩ => h ▸ hS s)
  have hnI1 : t₁ ∉ Ioo t₁ t₂ := fun h => lt_irrefl _ h.1
  have hnI2 : t₂ ∉ Ioo t₁ t₂ := fun h => lt_irrefl _ h.2
  have hnI3 : t₁ ∉ Ioo t₂ (t₁ + 1) := fun h => by linarith [h.1]
  have hnI4 : t₂ ∉ Ioo t₂ (t₁ + 1) := fun h => lt_irrefl _ h.1
  have hclB := hcl h12.le le_rfl h21
  rw [hc1] at hclB
  refine ⟨γ '' A', γ '' B', γ '' (p412eC '' Ioo t₁ t₂), γ '' (p412eC '' Ioo t₂ (t₁ + 1)),
    (isCompact_Icc.image hγc').image_of_continuousOn (hγc.mono hA'S),
    (isCompact_Icc.image hγc').image_of_continuousOn (hγc.mono hB'S), ?_, ?_,
    image_mono (image_mono Ioo_subset_Icc_self), image_mono (image_mono Ioo_subset_Icc_self),
    hsplit h12.le, by rw [hsplit h21.le, hc1, pair_comm],
    hnot le_rfl h21.le t₁ (Or.inl rfl) hnI1, hnot le_rfl h21.le t₂ (Or.inr rfl) hnI2,
    hnot h12.le le_rfl t₁ (Or.inl rfl) hnI3, hnot h12.le le_rfl t₂ (Or.inr rfl) hnI4,
    hpre _ _, hpre _ _, (hcl le_rfl h21.le h12).1, (hcl le_rfl h21.le h12).2, hclB.2, hclB.1⟩
  · rw [← image_union, ← image_union, Icc_union_Icc_eq_Icc h12.le h21.le, p412eC_image_Icc]
  · ext w
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, A', B', mem_image]
    constructor
    · rintro ⟨⟨_, ⟨s, hs, rfl⟩, rfl⟩, ⟨_, ⟨s', hs', rfl⟩, h⟩⟩
      rcases hval s ⟨hs.1, hs.2.trans h21.le⟩ s' ⟨h12.le.trans hs'.1, hs'.2⟩ h.symm with
        h' | ⟨h1, -⟩ | ⟨h1, -⟩
      · right; rw [show s = t₂ by linarith [hs.2, hs'.1, h'.symm ▸ hs'.1]]
      · left; rw [h1]
      · exfalso; linarith [hs.2]
    · rintro (rfl | rfl)
      · exact ⟨⟨_, ⟨t₁, ⟨le_rfl, h12.le⟩, rfl⟩, rfl⟩, ⟨_, ⟨t₁ + 1, ⟨h21.le, le_rfl⟩, rfl⟩,
          by rw [hc1]⟩⟩
      · exact ⟨⟨_, ⟨t₂, ⟨h12.le, le_rfl⟩, rfl⟩, rfl⟩, ⟨_, ⟨t₂, ⟨le_rfl, h21.le⟩, rfl⟩, rfl⟩⟩

end LQGMetric.GM
