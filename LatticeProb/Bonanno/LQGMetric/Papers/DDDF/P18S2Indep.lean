/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18S2Indep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2Site
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Indep
import LatticeProb.Bonanno.LQGMetric.Perc.Peierls

/-!
# DDDF Prop 18, Step 1: independence of far-apart sites (task P2-DDDF18P)

DDDF (arXiv:1904.08021, `tightness.tex` l. 903–904): "the states of sites at distance `≥ 2` are
independent" (finite range of dependence of `ψ`, DDDF l. 822, 838). Here: the badness of the site
`x` (rectangles around `sh x`, inside the box `[x₁, x₁+3] × [x₂, x₂+3]`) is an event of the field
`y ↦ ψ_{0,n}(sbox x y)` (`sbox x` = projection onto that box, `siteBad_eq_preimage`); for a finite
family of sites at `ℓ^∞`-distance `> 4` the corresponding events are independent
(`prob_iInter_sbox`): by induction on the family, the white noise restricted to a neighbourhood
of one box and to its complement are independent (`IsWhiteNoise.iIndepFun_of_pairwise_disjoint`,
`supportedIn_psiKernelL2_of_far`, `PsiSmall`), passed to the continuous version by
`indepFun_modification` (pattern of `indepFun_psiMN_clamp`, P16Indep.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- projection of `ℂ` onto the box `[x₁, x₁+3] × [x₂, x₂+3]` of the site `x` -/
def sbox (x : ℤ × ℤ) (y : ℂ) : ℂ :=
  ((projIcc (x.1 : ℝ) (x.1 + 3) (by linarith) y.re : ℝ) : ℂ) +
    ((projIcc (x.2 : ℝ) (x.2 + 3) (by linarith) y.im : ℝ) : ℂ) * Complex.I

lemma continuous_sbox (x : ℤ × ℤ) : Continuous (sbox x) :=
  (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
    (continuous_projIcc.comp Complex.continuous_re))).add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp
      (continuous_projIcc.comp Complex.continuous_im))).mul continuous_const)

lemma sbox_re (x : ℤ × ℤ) (y : ℂ) : (sbox x y).re ∈ Icc (x.1 : ℝ) (x.1 + 3) := by
  have := (projIcc (x.1 : ℝ) (x.1 + 3) (by linarith) y.re).2
  simpa [sbox] using this

lemma sbox_im (x : ℤ × ℤ) (y : ℂ) : (sbox x y).im ∈ Icc (x.2 : ℝ) (x.2 + 3) := by
  have := (projIcc (x.2 : ℝ) (x.2 + 3) (by linarith) y.im).2
  simpa [sbox] using this

lemma sbox_of_mem {x : ℤ × ℤ} {y : ℂ} (h1 : y.re ∈ Icc (x.1 : ℝ) (x.1 + 3))
    (h2 : y.im ∈ Icc (x.2 : ℝ) (x.2 + 3)) : sbox x y = y := by
  apply Complex.ext <;> simp [sbox, projIcc_of_mem _ h1, projIcc_of_mem _ h2]

/-- an event `{ℓ < L(R)}` for `R` in the box of `x` is an event of `ψ ∘ sbox x` -/
lemma exists_set_gt_lenObs {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (ℓ : ℝ)
    (x : ℤ × ℤ) (R : MarkedRect)
    (hR : ∀ y ∈ R.toSet, y.re ∈ Icc (x.1 : ℝ) (x.1 + 3) ∧ y.im ∈ Icc (x.2 : ℝ) (x.2 + 3)) :
    ∃ T : Set (ℂ → ℝ), MeasurableSet T ∧
      ∀ ω, (ℓ < lenObs ξ Y R ω ↔ (fun y => Y (sbox x y) ω) ∈ T) := by
  obtain ⟨T, hT, hiff⟩ := exists_set_crossLenIn (ξ := ξ) (MarkedRect.isCompact_toSet R)
    R.side₁ R.side₂ (S := {v | ℓ < v.toReal})
    (measurableSet_lt measurable_const ENNReal.measurable_toReal)
  refine ⟨T, hT, fun ω => ?_⟩
  have e : crossLenIn ξ (fun y => Y y ω) R.toSet R.side₁ R.side₂ =
      crossLenIn ξ (fun y => Y (sbox x y) ω) R.toSet R.side₁ R.side₂ :=
    crossLenIn_congr' fun y hy => by rw [sbox_of_mem (hR y hy).1 (hR y hy).2]
  have h := hiff (fun y => Y (sbox x y) ω) ((hYc ω).comp (continuous_sbox x))
  show ℓ < (rectLen ξ (fun y => Y y ω) R).toReal ↔ _
  rw [rectLen, e]; exact h

/-- **the badness of the site `x` is an event of `ψ ∘ sbox x`** -/
theorem siteBad_eq_preimage {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (ℓ : ℝ)
    (x : ℤ × ℤ) :
    ∃ T : Set (ℂ → ℝ), MeasurableSet T ∧
      siteBad (ξ := ξ) Y ℓ (sh x) = {ω | (fun y => Y (sbox x y) ω) ∈ T} := by
  have hx1 : ((x.1 + 1 : ℤ) : ℝ) = (x.1 : ℝ) + 1 := by push_cast; ring
  have hx2 : ((x.2 + 1 : ℤ) : ℝ) = (x.2 : ℝ) + 1 := by push_cast; ring
  have mk : ∀ R : MarkedRect, R.x0 = (x.1 : ℝ) ∨ R.x0 = (x.1 : ℝ) + 2 →
      R.y0 = (x.2 : ℝ) ∨ R.y0 = (x.2 : ℝ) + 2 → R.x0 + R.w ≤ x.1 + 3 → R.y0 + R.h ≤ x.2 + 3 →
      ∀ y ∈ R.toSet, y.re ∈ Icc (x.1 : ℝ) (x.1 + 3) ∧ y.im ∈ Icc (x.2 : ℝ) (x.2 + 3) := by
    intro R h1 h2 h3 h4 y hy
    rw [mem_toSet_iff] at hy
    refine ⟨⟨?_, by linarith [hy.1.2]⟩, ⟨?_, by linarith [hy.2.2]⟩⟩
    · rcases h1 with h1 | h1 <;> linarith [hy.1.1]
    · rcases h2 with h2 | h2 <;> linarith [hy.2.1]
  obtain ⟨T1, hT1, h1⟩ := exists_set_gt_lenObs (ξ := ξ) hYc ℓ x (sB (sh x))
    (mk _ (by left; simp [sB, sh]) (by left; simp [sB, sh]) (by simp [sB, sh] <;> linarith)
      (by simp [sB, sh]))
  obtain ⟨T2, hT2, h2⟩ := exists_set_gt_lenObs (ξ := ξ) hYc ℓ x (sT (sh x))
    (mk _ (by left; simp [sT, sh]) (by right; simp [sT, sh] <;> ring) (by simp [sT, sh] <;> linarith)
      (by simp [sT, sh] <;> linarith))
  obtain ⟨T3, hT3, h3⟩ := exists_set_gt_lenObs (ξ := ξ) hYc ℓ x (sL (sh x))
    (mk _ (by left; simp [sL, sh]) (by left; simp [sL, sh]) (by simp [sL, sh])
      (by simp [sL, sh] <;> linarith))
  obtain ⟨T4, hT4, h4⟩ := exists_set_gt_lenObs (ξ := ξ) hYc ℓ x (sR (sh x))
    (mk _ (by right; simp [sR, sh] <;> ring) (by left; simp [sR, sh]) (by simp [sR, sh] <;> linarith)
      (by simp [sR, sh] <;> linarith))
  refine ⟨T1 ∪ T2 ∪ T3 ∪ T4, ((hT1.union hT2).union hT3).union hT4, ?_⟩
  ext ω
  simp only [siteBad, mem_union, mem_ofPred_eq, h1, h2, h3, h4]

/-- the neighbourhood of the box of `a` carrying the noise of `ψ` on that box -/
def nbhdBox (a : ℤ × ℤ) : Set (ℝ × ℂ) :=
  {p | (a.1 : ℝ) - 1 / 2 < p.2.re ∧ p.2.re < a.1 + 7 / 2 ∧ (a.2 : ℝ) - 1 / 2 < p.2.im ∧
    p.2.im < a.2 + 7 / 2}

lemma measurableSet_nbhdBox (a : ℤ × ℤ) : MeasurableSet (nbhdBox a) := by
  have hr : Measurable fun p : ℝ × ℂ => p.2.re := Complex.measurable_re.comp measurable_snd
  have hi : Measurable fun p : ℝ × ℂ => p.2.im := Complex.measurable_im.comp measurable_snd
  exact (measurableSet_lt measurable_const hr).inter ((measurableSet_lt hr measurable_const).inter
    ((measurableSet_lt measurable_const hi).inter (measurableSet_lt hi measurable_const)))

lemma near_box_dist (a : ℤ × ℤ) (y : ℂ) (q : ℝ × ℂ) (hq : q ∉ nbhdBox a) :
    1 / 2 ≤ ‖sbox a y - q.2‖ := by
  set p := q.2
  have hre := sbox_re a y
  have him := sbox_im a y
  have h1 := Complex.abs_re_le_norm (sbox a y - p)
  have h2 := Complex.abs_im_le_norm (sbox a y - p)
  rw [Complex.sub_re, abs_le] at h1
  rw [Complex.sub_im, abs_le] at h2
  have hp' := hq
  simp only [nbhdBox, mem_ofPred_eq, not_and_or, not_lt] at hp'
  rcases hp' with hp' | hp' | hp' | hp'
  · linarith [hre.1, h1.1]
  · linarith [hre.2, h1.2]
  · linarith [him.1, h2.1]
  · linarith [him.2, h2.2]

lemma far_box_dist (a x : ℤ × ℤ) (hfar : PercFar 4 a x) (y : ℂ) (q : ℝ × ℂ)
    (hq : q ∈ nbhdBox a) : 1 / 2 ≤ ‖sbox x y - q.2‖ := by
  set p := q.2
  have hp : (a.1 : ℝ) - 1 / 2 < p.re ∧ p.re < a.1 + 7 / 2 ∧ (a.2 : ℝ) - 1 / 2 < p.im ∧
      p.im < a.2 + 7 / 2 := hq
  have hre := sbox_re x y
  have him := sbox_im x y
  have h1 := Complex.abs_re_le_norm (sbox x y - p)
  have h2 := Complex.abs_im_le_norm (sbox x y - p)
  rw [Complex.sub_re, abs_le] at h1
  rw [Complex.sub_im, abs_le] at h2
  obtain ⟨p1, p2, p3, p4⟩ := hp
  unfold PercFar at hfar
  rcases hfar with h | h | h | h
  · have : (5 : ℝ) ≤ (a.1 : ℝ) - x.1 := by
      have : (5 : ℤ) ≤ a.1 - x.1 := by push_cast at h; omega
      exact_mod_cast this
    linarith [hre.2, h1.2]
  · have : (5 : ℝ) ≤ (x.1 : ℝ) - a.1 := by
      have : (5 : ℤ) ≤ x.1 - a.1 := by push_cast at h; omega
      exact_mod_cast this
    linarith [hre.1, h1.1]
  · have : (5 : ℝ) ≤ (a.2 : ℝ) - x.2 := by
      have : (5 : ℤ) ≤ a.2 - x.2 := by push_cast at h; omega
      exact_mod_cast this
    linarith [him.2, h2.2]
  · have : (5 : ℝ) ≤ (x.2 : ℝ) - a.2 := by
      have : (5 : ℤ) ≤ x.2 - a.2 := by push_cast at h; omega
      exact_mod_cast this
    linarith [him.1, h2.1]

/-- **independence of the box fields of `a` and of finitely many far sites** -/
theorem indepFun_sbox {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams)
    (hQ : PsiSmall Q) (n : ℕ) (a : ℤ × ℤ) (F : Finset (ℤ × ℤ)) (hF : ∀ x ∈ F, PercFar 4 a x) :
    IndepFun (fun ω y => psiMN Q W P 0 n (sbox a y) ω)
      (fun ω (q : F × ℂ) => psiMN Q W P 0 n (sbox q.1 q.2) ω) P := by
  have := hW.isProbabilityMeasure
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  set a' : ℝ := (2 : ℝ)⁻¹ ^ n
  set b : ℝ := (2 : ℝ)⁻¹ ^ 0
  have ha : 0 < a' := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hb : b ≤ 1 := by simp [b]
  let A : Bool → Set (ℝ × ℂ) := fun i => if i then nbhdBox a else (nbhdBox a)ᶜ
  have hA : Pairwise fun i j => Disjoint (A i) (A j) := by
    rintro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact absurd rfl hij
  have hs₁ : ∀ y : ℂ, SupportedIn (A true) (Q.psiKernelL2 a' b (sbox a y)) := fun y =>
    supportedIn_psiKernelL2_of_far Q hQ ha hb0 hb _ (measurableSet_nbhdBox a) fun p hp =>
      near_box_dist a y p hp
  have hs₂ : ∀ q : F × ℂ, SupportedIn (A false) (Q.psiKernelL2 a' b (sbox q.1 q.2)) := fun q =>
    supportedIn_psiKernelL2_of_far Q hQ ha hb0 hb _ (measurableSet_nbhdBox a).compl
      fun p hp => far_box_dist a q.1 (hF q.1 q.1.2) q.2 p (not_not.1 hp)
  have hI := (hW.iIndepFun_of_pairwise_disjoint hA).indepFun (show true ≠ false by decide)
  let Φ₁ : ({f // SupportedIn (A true) f} → ℝ) → ℂ → ℝ :=
    fun G y => Real.sqrt Real.pi * G ⟨Q.psiKernelL2 a' b (sbox a y), hs₁ y⟩
  let Φ₂ : ({f // SupportedIn (A false) f} → ℝ) → F × ℂ → ℝ :=
    fun G q => Real.sqrt Real.pi * G ⟨Q.psiKernelL2 a' b (sbox q.1 q.2), hs₂ q⟩
  have hΦ₁ : Measurable Φ₁ := measurable_pi_iff.mpr fun y => (measurable_pi_apply _).const_mul _
  have hΦ₂ : Measurable Φ₂ := measurable_pi_iff.mpr fun q => (measurable_pi_apply _).const_mul _
  have h3 := hI.comp hΦ₁ hΦ₂
  have h4 : IndepFun (fun ω (y : ℂ) => Real.sqrt Real.pi * W (Q.psiKernelL2 a' b (sbox a y)) ω)
      (fun ω (q : F × ℂ) => Real.sqrt Real.pi * W (Q.psiKernelL2 a' b (sbox q.1 q.2)) ω) P := h3
  have e1 : ∀ y : ℂ, (fun ω => psiMN Q W P 0 n (sbox a y) ω) =ᵐ[P]
      fun ω => Real.sqrt Real.pi * W (Q.psiKernelL2 a' b (sbox a y)) ω := fun y => hψ.ae_eq _
  have e2 : ∀ q : F × ℂ, (fun ω => psiMN Q W P 0 n (sbox q.1 q.2) ω) =ᵐ[P]
      fun ω => Real.sqrt Real.pi * W (Q.psiKernelL2 a' b (sbox q.1 q.2)) ω := fun q => hψ.ae_eq _
  have m1 : ∀ y : ℂ, Measurable fun ω => Real.sqrt Real.pi * W (Q.psiKernelL2 a' b (sbox a y)) ω :=
    fun y => (hW.measurable _).const_mul _
  have m2 : ∀ y : ℂ, Measurable fun ω => psiMN Q W P 0 n (sbox a y) ω := fun y => hψ.meas _
  have m3 : ∀ q : F × ℂ, Measurable fun ω =>
      Real.sqrt Real.pi * W (Q.psiKernelL2 a' b (sbox q.1 q.2)) ω :=
    fun y => (hW.measurable _).const_mul _
  have m4 : ∀ q : F × ℂ, Measurable fun ω => psiMN Q W P 0 n (sbox q.1 q.2) ω := fun q => hψ.meas _
  exact indepFun_modification m1 m2 m3 m4 e1 e2 h4

/-- **product formula for far-apart sites** (DDDF l. 903–904) -/
theorem prob_iInter_sbox {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams)
    (hQ : PsiSmall Q) (n : ℕ) (T : ℤ × ℤ → Set (ℂ → ℝ)) (hT : ∀ x, MeasurableSet (T x))
    (F : Finset (ℤ × ℤ)) (hF : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 4 x y) :
    P (⋂ x ∈ F, {ω | (fun y => psiMN Q W P 0 n (sbox x y) ω) ∈ T x}) =
      ∏ x ∈ F, P {ω | (fun y => psiMN Q W P 0 n (sbox x y) ω) ∈ T x} := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [hW.isProbabilityMeasure.measure_univ]
  | @insert a F haF ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert haF,
      ← ih fun x hx y hy hxy => hF x (Finset.mem_insert_of_mem hx) y
        (Finset.mem_insert_of_mem hy) hxy]
    have hind := indepFun_sbox hW Q hQ n a F fun x hx =>
      hF a (Finset.mem_insert_self _ _) x (Finset.mem_insert_of_mem hx)
        (fun h => haF (h ▸ hx))
    set T' : Set (F × ℂ → ℝ) := {h | ∀ x : F, (fun y => h (x, y)) ∈ T x}
    have hT' : MeasurableSet T' := by
      have : T' = ⋂ x : F, (fun h : F × ℂ → ℝ => fun y => h (x, y)) ⁻¹' T x := by
        ext h; simp [T']
      rw [this]
      exact MeasurableSet.iInter fun x =>
        (measurable_pi_iff.2 fun y => measurable_pi_apply (x, y)) (hT x)
    have e : (⋂ x ∈ F, {ω | (fun y => psiMN Q W P 0 n (sbox x y) ω) ∈ T x}) =
        (fun ω (q : F × ℂ) => psiMN Q W P 0 n (sbox q.1 q.2) ω) ⁻¹' T' := by
      ext ω; simp [T']
    rw [e]
    exact hind.measure_inter_preimage_eq_mul (T a) T' (hT a) hT'

end DDDF
end LQGMetric
