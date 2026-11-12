/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.BasicsReflection at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Schwarz reflection consequences of `painleveRealLine` (EXT-CA node A3)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.A, node **A3**.

(a) `exists_reflection_extension`: if `g` is holomorphic on `ℍ ∩ B(x, r)` (`x ∈ ℝ`), continuous
on `ℍ̄ ∩ B(x, r)` and real on `ℝ ∩ B(x, r)`, then `g` extends to a holomorphic function on
`B(x, r)` commuting with `conj` (Schwarz reflection principle; Ahlfors, *Complex Analysis*,
3rd ed. 1979, Ch. 4 §6.5 "The reflection principle", cited as "Ahlfors p. 171" in
Pommerenke, *Univalent Functions* 1975, `literature/Pommerenke_UnivalentFunctions_1975.txt`).
Ahlfors proves holomorphy across `ℝ` by the Poisson integral; we use Morera's theorem instead
(`painleveRealLine`, the tool fixed by the blueprint). The extension is `z ↦ conj (g (conj z))` on the lower half;
holomorphy across the real axis is `painleveRealLine` (Morera).

(b) `eqOn_const_of_eq_const_on_Ioo`: if moreover `g ≡ c` on a nondegenerate real interval in
`B(x, r)`, then `g ≡ c` on `ℍ̄ ∩ B(x, r)` (identity theorem for the extension).
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped ComplexConjugate

namespace QuantumZipper.CA

/-- The Schwarz reflection of `g` across `ℝ`: `g` on `{Im ≥ 0}`, `conj ∘ g ∘ conj` below. -/
def schwarzReflect (g : ℂ → ℂ) (z : ℂ) : ℂ := if 0 ≤ z.im then g z else conj (g (conj z))

theorem conj_mem_ball_ofReal {x r : ℝ} {z : ℂ} (hz : z ∈ ball (x : ℂ) r) :
    conj z ∈ ball (x : ℂ) r := by
  rw [mem_ball, ← conj_ofReal, dist_conj_conj]; exact hz

/-- **Schwarz reflection** (A3 (a)). -/
theorem exists_reflection_extension {g : ℂ → ℂ} {x r : ℝ}
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (x : ℂ) r) ∧ EqOn G g (Hbar ∩ ball (x : ℂ) r) ∧
      ∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z) := by
  set B := ball (x : ℂ) r
  set G := schwarzReflect g with hG
  have hHo : IsOpen (H ∩ B) := isOpen_H.inter isOpen_ball
  -- continuity
  have hcl : closure {a : ℂ | ¬ 0 ≤ a.im} ⊆ {a : ℂ | a.im ≤ 0} :=
    closure_minimal (fun (z : ℂ) (hz : ¬ 0 ≤ z.im) => (not_le.1 hz).le)
      (isClosed_le continuous_im continuous_const)
  have hcont : ContinuousOn G B := by
    refine ContinuousOn.if ?_ ?_ ?_
    · intro a ⟨haB, hfr⟩
      have h1 : 0 ≤ a.im := closure_minimal (fun _ h => h) isClosed_Hbar
        (frontier_subset_closure hfr)
      have h2 : a.im ≤ 0 := by
        have hfr' := hfr
        rw [← frontier_compl] at hfr'
        have := frontier_subset_closure hfr'
        exact hcl this
      have ha : a.im = 0 := le_antisymm h2 h1
      rw [conj_eq_iff_im.2 ha]
      exact (conj_eq_iff_im.2 (hreal a haB ha)).symm
    · exact hc.mono fun a ⟨haB, ha⟩ =>
        ⟨closure_minimal (fun _ h => h) isClosed_Hbar ha, haB⟩
    · have hsub : B ∩ closure {a : ℂ | ¬ 0 ≤ a.im} ⊆ {a : ℂ | a.im ≤ 0} ∩ B := fun a ⟨haB, ha⟩ =>
        ⟨hcl ha, haB⟩
      refine ContinuousOn.mono ?_ hsub
      refine continuous_conj.comp_continuousOn (hc.comp continuous_conj.continuousOn ?_)
      intro a ⟨ha, haB⟩
      exact ⟨show 0 ≤ (conj a).im by simpa using ha, conj_mem_ball_ofReal haB⟩
  -- holomorphy off the real axis
  have hdiff : DifferentiableOn ℂ G (B \ {z | z.im = 0}) := by
    intro z ⟨hzB, hz0⟩
    have hz0 : z.im ≠ 0 := hz0
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases lt_or_gt_of_ne hz0 with hneg | hpos
    · -- lower half-plane
      have hcz : conj z ∈ H ∩ B := ⟨show 0 < (conj z).im by simp; linarith,
        conj_mem_ball_ofReal hzB⟩
      have h1 : DifferentiableAt ℂ g (conj z) := hd.differentiableAt (hHo.mem_nhds hcz)
      have h2 := h1.conj_conj
      rw [conj_conj] at h2
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds
        (show z ∈ {w : ℂ | w.im < 0} from hneg)] with w hw
      have hw' : ¬ 0 ≤ w.im := not_le.2 hw
      simp [hG, schwarzReflect, hw']
    · have h1 : DifferentiableAt ℂ g z := hd.differentiableAt (hHo.mem_nhds ⟨hpos, hzB⟩)
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds
        (show z ∈ {w : ℂ | 0 < w.im} from hpos)] with w hw
      have hw' : 0 ≤ w.im := le_of_lt hw
      simp [hG, schwarzReflect, hw']
  refine ⟨G, painleveRealLine G B isOpen_ball hcont hdiff, ?_, ?_⟩
  · intro z ⟨hz, _⟩
    have hz' : 0 ≤ z.im := hz
    simp [hG, schwarzReflect, hz']
  · intro z hzB
    rcases lt_trichotomy z.im 0 with hneg | h0 | hpos
    · have h1 : 0 ≤ (conj z).im := by simp; linarith
      have h2 : ¬ 0 ≤ z.im := not_le.2 hneg
      simp only [hG, schwarzReflect, h1, h2, ↓reduceIte, conj_conj]
    · rw [conj_eq_iff_im.2 h0]
      have h1 : 0 ≤ z.im := h0.ge
      simp only [hG, schwarzReflect, h1, ↓reduceIte]
      exact (conj_eq_iff_im.2 (hreal z hzB h0)).symm
    · have h1 : ¬ 0 ≤ (conj z).im := by simp; linarith
      have h2 : 0 ≤ z.im := hpos.le
      simp only [hG, schwarzReflect, h1, h2, ↓reduceIte, conj_conj]

/-- **Identity theorem at the boundary** (A3 (b)): a function as in
`exists_reflection_extension` that is constant on a nondegenerate real interval inside the
ball is constant on `ℍ̄ ∩ B(x, r)`. -/
theorem eqOn_const_of_eq_const_on_Ioo {g : ℂ → ℂ} {x r : ℝ}
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0)
    {a b : ℝ} (hab : a < b) {c : ℂ}
    (hI : ∀ t ∈ Ioo a b, (t : ℂ) ∈ ball (x : ℂ) r ∧ g t = c) :
    ∀ z ∈ Hbar ∩ ball (x : ℂ) r, g z = c := by
  obtain ⟨G, hG, hGg, -⟩ := exists_reflection_extension hd hc hreal
  have hA : AnalyticOnNhd ℂ G (ball (x : ℂ) r) := hG.analyticOnNhd isOpen_ball
  set t₀ : ℝ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := ⟨by simp [t₀]; linarith, by simp [t₀]; linarith⟩
  have hreal_mem : ∀ t ∈ Ioo a b, (t : ℂ) ∈ Hbar ∩ ball (x : ℂ) r := fun t ht =>
    ⟨show (0 : ℝ) ≤ (t : ℂ).im by simp, (hI t ht).1⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] (t₀ : ℂ), G z = c := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] t₀) (𝓝[≠] (t₀ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_ofReal.tendsto t₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact fun h => ht (ofReal_injective h)
    refine htend.frequently ?_
    refine Eventually.frequently ?_
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds ht₀.1 ht₀.2)] with t ht
    rw [hGg (hreal_mem t ht)]
    exact (hI t ht).2
  have heq := hA.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    (convex_ball _ _).isPreconnected (hI t₀ ht₀).1 hfreq
  intro z hz
  rw [← hGg hz]
  exact heq hz.2

end QuantumZipper.CA
