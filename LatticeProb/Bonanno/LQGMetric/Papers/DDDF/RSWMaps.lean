/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWMaps at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Node
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12

/-!
# RSW geometry: the finite family of conformal comparisons (DDDF Prop 14, Steps 1–2)

Task P2-DDDFRSW. DDDF `tightness.tex` l. 790–806 (DF arXiv:1809.02607, proof of Thm 3.1,
DF:624–678): by Lemma 11 iterated `p` times (`forces_iter`) and Lemma 12′ (`L12.lemma12'`),
there is a finite family `τ` of compact sets `K_τ` with marked compact arcs `A_τ, B_τ` and
conformal maps `F_τ` (as in Prop 10, `P10Map`) such that
* every left–right crossing of `R_{a,b}` has a sub-arc crossing some `(K_τ, A_τ, B_τ)`, so
  `min_τ L(K_τ, A_τ, B_τ) ≤ L(R_{a,b})` (`rsw_geom`, item 2);
* every crossing of `(F_τ(K_τ), F_τ(A_τ), F_τ(B_τ))` contains a left–right crossing of
  `R_{a',b'}`, so `L(R_{a',b'}) ≤ L(F_τ(K_τ), F_τ(A_τ), F_τ(B_τ))` (item 3).
`K_τ = g⁻¹(K)`, `A_τ = g⁻¹(A_i)`, `B_τ = g⁻¹(B_j)`, `F_τ = F_{ij} ∘ g` for a rigid motion `g`
(this replaces DDDF's "rectangles isometric to `[0, a/2^p] × [0, b/2^p]`" together with the law
invariance of `φ_{0,n}` under rigid motions by applying Prop 10 directly to the moved domains,
which Prop 10 allows since it holds for every `K` and `F`; DEV D-DDDF-19).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF

theorem isometry_mot {g : ℂ × ℂ} (hg : ‖g.1‖ = 1) : Isometry (mot g) :=
  Isometry.of_dist_eq fun x y => by
    simp only [mot, dist_eq_norm]
    rw [show g.1 * x + g.2 - (g.1 * y + g.2) = g.1 * (x - y) by ring, norm_mul, hg, one_mul]

theorem hasDerivAt_mot (g : ℂ × ℂ) (z : ℂ) : HasDerivAt (mot g) g.1 z := by
  show HasDerivAt (fun z => g.1 * z + g.2) g.1 z
  simpa using ((hasDerivAt_id z).const_mul g.1).add_const g.2

theorem surjective_mot {g : ℂ × ℂ} (hg : ‖g.1‖ = 1) : Function.Surjective (mot g) := by
  have h0 : g.1 ≠ 0 := by intro h; rw [h, norm_zero] at hg; exact zero_ne_one hg
  intro w
  exact ⟨(w - g.2) / g.1, by simp only [mot]; field_simp; ring⟩

theorem image_comp_mot_preimage {g : ℂ × ℂ} (hg : ‖g.1‖ = 1) (F : ℂ → ℂ) (X : Set ℂ) :
    (F ∘ mot g) '' (mot g ⁻¹' X) = F '' X := by
  rw [image_comp, image_preimage_eq X (surjective_mot hg)]

/-- Prop 10's hypotheses are invariant under precomposition with a rigid motion -/
theorem p10Map_comp_mot {K U : Set ℂ} {F : ℂ → ℂ} {g : ℂ × ℂ} (hg : ‖g.1‖ = 1)
    (h : P10Map K U F) : P10Map (mot g ⁻¹' K) (mot g ⁻¹' U) (F ∘ mot g) := by
  have hiso := isometry_mot hg
  have hc : Continuous (mot g) := hiso.continuous
  obtain ⟨M, hM⟩ := h.deriv_bd
  have hU' : IsOpen (mot g ⁻¹' U) := h.isOpen.preimage hc
  have hF' : ∀ z ∈ mot g ⁻¹' U, deriv (F ∘ mot g) z = deriv F (mot g z) * g.1 := fun z hz => by
    rw [deriv_comp z ((h.diff _ hz).differentiableAt (h.isOpen.mem_nhds hz))
      (hasDerivAt_mot g z).differentiableAt, (hasDerivAt_mot g z).deriv]
  have hF'' : ∀ z ∈ mot g ⁻¹' U,
      deriv (deriv (F ∘ mot g)) z = deriv (deriv F) (mot g z) * g.1 * g.1 := fun z hz => by
    have heq : deriv (F ∘ mot g) =ᶠ[𝓝 z] fun w => deriv F (mot g w) * g.1 :=
      Filter.eventually_of_mem (hU'.mem_nhds hz) fun w hw => hF' w hw
    rw [heq.deriv_eq]
    have hdd : DifferentiableAt ℂ (deriv F) (mot g z) :=
      ((h.diff.deriv h.isOpen) _ hz).differentiableAt (h.isOpen.mem_nhds hz)
    exact ((hdd.hasDerivAt.comp z (hasDerivAt_mot g z)).mul_const g.1).deriv
  refine ⟨hU', hiso.antilipschitzWith.isBounded_preimage h.bdd, preimage_mono h.sub,
    h.diff.comp (fun z _ => (hasDerivAt_mot g z).differentiableAt.differentiableWithinAt)
      (mapsTo_preimage _ _),
    fun z hz w hw e => hiso.injective (h.inj hz hw e), ⟨M, fun z hz => ?_⟩⟩
  rw [hF' z hz, hF'' z hz, norm_mul, norm_mul, norm_mul, hg]
  simp only [mul_one]
  exact hM _ hz

/-- **The RSW geometry** (DDDF l. 790–806, Lemma 11 iterated + Lemma 12′). -/
theorem rsw_geom {a b a' b' : ℝ} (ha : 0 < a) (hab : a < b) (ha' : 0 < a') (hb' : 0 < b') :
    ∃ (κ : Type) (_ : Fintype κ) (K A B U : κ → Set ℂ) (F : κ → ℂ → ℂ),
      (∀ τ, IsCompact (K τ) ∧ IsCompact (A τ) ∧ IsCompact (B τ) ∧ A τ ⊆ K τ ∧ B τ ⊆ K τ ∧
        P10Map (K τ) (U τ) (F τ)) ∧
      (∀ (ξ : ℝ) (f : ℂ → ℝ),
        ⨅ τ, crossLenIn ξ f (K τ) (A τ) (B τ) ≤ rectLen ξ f (rectAB a b)) ∧
      (∀ (ξ : ℝ) (f : ℂ → ℝ) τ,
        rectLen ξ f (rectAB a' b') ≤ crossLenIn ξ f (F τ '' K τ) (F τ '' A τ) (F τ '' B τ)) := by
  obtain ⟨p, m, K, A, B, -, -, hK, hA, hB, hcross, hmaps⟩ :=
    L12.lemma12' ha (show 0 < b by linarith) ha' hb'
  choose F U hUo hUb hKU hFd hFi hFC hFcross using hmaps
  set S : Fin m × Fin m → Set ℂ × Set ℂ × Set ℂ := fun ij => (K, A ij.1, B ij.2)
  have hmot1 : ∀ x : ℂ, mot (1, 0) x = x := fun x => by simp [mot]
  have hbase : Forces (a / 2 ^ p) (b / 2 ^ p) {((1 : ℂ), (0 : ℂ))} S := by
    refine ⟨finite_singleton _, by simp, fun γ hγ h0 h1 => ?_⟩
    obtain ⟨i, j, s, t, hs0, hst, ht1, hKs, hAs, hBt⟩ := hcross γ hγ h0 h1
    refine ⟨(1, 0), rfl, (i, j), s, ⟨hs0, hst.trans ht1⟩, t, ⟨hs0.trans hst, ht1⟩,
      fun u hu => ?_, ?_, ?_⟩
    · rw [uIcc_of_le hst] at hu
      simp only [S, mem_preimage, hmot1]; exact hKs u hu
    · simp only [S, mem_preimage, hmot1]; exact hAs
    · simp only [S, mem_preimage, hmot1]; exact hBt
  obtain ⟨G, hG⟩ := forces_iter p ha hab hbase
  letI : Fintype ↥G := hG.1.fintype
  refine ⟨↥G × (Fin m × Fin m), inferInstance, fun τ => mot τ.1 ⁻¹' K,
    fun τ => mot τ.1 ⁻¹' A τ.2.1, fun τ => mot τ.1 ⁻¹' B τ.2.2,
    fun τ => mot τ.1 ⁻¹' U τ.2.1 τ.2.2, fun τ => F τ.2.1 τ.2.2 ∘ mot τ.1, ?_, ?_, ?_⟩
  · intro τ
    have hg := hG.2.1 _ τ.1.2
    have hce := (isometry_mot hg).isClosedEmbedding
    exact ⟨hce.isCompact_preimage hK, hce.isCompact_preimage (hA _).1,
      hce.isCompact_preimage (hB _).1, preimage_mono (hA _).2, preimage_mono (hB _).2,
      p10Map_comp_mot hg ⟨hUo _ _, hUb _ _, hKU _ _, hFd _ _, hFi _ _, hFC _ _⟩⟩
  · intro ξ f
    refine le_crossLenIn fun P hP => ?_
    obtain ⟨z, hz, w, hw, hPc, hPU⟩ := hP
    have hγ : ∀ τ, pathOf hPc τ ∈ RectCross.rect 0 a 0 b := fun τ => by
      have := hPU τ τ.2
      simp only [rectAB, MarkedRect.toSet, Complex.mem_reProdIm, zero_add] at this
      exact this
    have hz0 : z.re = 0 := by
      simp only [rectAB, MarkedRect.side₁, ite_true, Complex.mem_reProdIm] at hz; exact hz.1
    have hw1 : w.re = a := by
      simp only [rectAB, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, zero_add] at hw
      exact hw.1
    obtain ⟨g, hg, ij, hcd⟩ := hG.2.2 (pathOf hPc) hγ hz0 hw1
    exact iInf_le_of_le (⟨g, hg⟩, ij) (crossLenIn_le_of_crossData hPc hcd)
  · intro ξ f τ
    have hg := hG.2.1 _ τ.1.2
    simp only [image_comp_mot_preimage hg]
    refine le_crossLenIn fun P hP => ?_
    obtain ⟨z, hz, w, hw, hPc, hPU⟩ := hP
    obtain ⟨s, t, hs0, hst, ht1, hR, hdir⟩ :=
      hFcross τ.2.1 τ.2.2 (pathOf hPc) (fun σ => hPU σ σ.2) hz hw
    have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
    have hR' : ∀ u ∈ Icc s t, P u ∈ RectCross.rect 0 a' 0 b' := fun u hu => by
      have := hR u hu
      rwa [pathOf_extend hPc ⟨hs0.trans hu.1, hu.2.trans ht1⟩] at this
    have hmemR : ∀ u ∈ Icc s t, P u ∈ (rectAB a' b').toSet := fun u hu => by
      simp only [rectAB, MarkedRect.toSet, Complex.mem_reProdIm, zero_add]; exact hR' u hu
    rw [pathOf_extend hPc hs, pathOf_extend hPc ht] at hdir
    have hside₁ : ∀ u ∈ Icc s t, (P u).re = 0 → P u ∈ (rectAB a' b').side₁ := fun u hu h => by
      simp only [rectAB, MarkedRect.side₁, ite_true, Complex.mem_reProdIm, zero_add,
        mem_singleton_iff]; exact ⟨h, (hR' u hu).2⟩
    have hside₂ : ∀ u ∈ Icc s t, (P u).re = a' → P u ∈ (rectAB a' b').side₂ := fun u hu h => by
      simp only [rectAB, MarkedRect.side₂, ite_true, Complex.mem_reProdIm, zero_add,
        mem_singleton_iff]; exact ⟨h, (hR' u hu).2⟩
    have hsI : s ∈ Icc s t := ⟨le_rfl, hst⟩
    have htI : t ∈ Icc s t := ⟨hst, le_rfl⟩
    rcases hdir with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · exact crossLenIn_le_of_sub hPc hs ht (fun u hu => hmemR u (by rwa [uIcc_of_le hst] at hu))
        (hside₁ s hsI e0) (hside₂ t htI e1)
    · exact crossLenIn_le_of_sub hPc ht hs
        (fun u hu => hmemR u (by rwa [uIcc_comm, uIcc_of_le hst] at hu))
        (hside₁ t htI e1) (hside₂ s hsI e0)

end DDDF
end LQGMetric
