/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8Copy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Trans
import LatticeProb.Bonanno.LQGMetric.Prob.CondCopies
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsLM

/-!
# LM Corollary 1.8, step 1: the copy pair `(D, D̃)` is ξ-additive (task P2-LMC18)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Corollary 1.8, l. 323–328: "We first claim that `(D, D̃)` is a
pair of ξ-additive local metrics for `h|_U`. We know from Definition 1.5 that for each `z ∈ U` and
each `r > 0` …, each of `e^{−ξh_r(z)} D` and `e^{−ξh_r(z)} D̃` is individually local for
`h|_U − h_r(z)`. Since `B_1(0), B_r(z) ⊂ U`, it follows that `h|_U` and `h|_U − h_r(z)` determine
each other. Since `e^{−ξh_r(z)} D` and `e^{−ξh_r(z)} D̃` are conditionally independent given
`h|_U`, they are also conditionally independent given `h|_U − h_r(z)`. By Lemma 1.4, these two
metrics are jointly local for `h|_U − h_r(z)`."

The pair is the canonical copy `condCopyMeasure D h P` on `Ω × ContMetric` (`D̃ = Prod.snd`).
Main result: `c18_xiAdditive_copy` (`LMLem1_4` and a.s. length of `D̃` as inputs). That `D̃` is
"individually local" is `c18_jl_transfer` (locality is a property of the law of `(h, D)`,
`C1_8Trans.lean`). That `D̃` is a.s. a length metric is not derivable from the law in this
formalization (the set of length metrics is not known to be measurable), see `CopyAeLength`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip

/-! ## Measurable internal metrics on the canonical space -/

/-- a measurable version of `d ↦ d(·,·;W)` (equal to it on length metrics, `W` open) -/
def c18J (W : Set ℂ) (d : ContMetric) : ℂ → ℂ → ℝ≥0∞ := by
  classical
  exact if hW : IsOpen W then fun u v => (measurable_internal hW).choose (d, u, v)
    else fun _ _ => 0

lemma measurable_c18J {W : Set ℂ} (hW : IsOpen W) : Measurable (c18J W) := by
  have hF := (measurable_internal hW).choose_spec.1
  unfold c18J
  simp only [dif_pos hW]
  exact measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
    hF.comp (measurable_id.prodMk measurable_const)

lemma c18J_eq {W : Set ℂ} (hW : IsOpen W) {d : ContMetric} (hd : d.IsLength) :
    c18J W d = d.internal W := by
  simp only [c18J, dif_pos hW]
  funext u v
  exact ((measurable_internal hW).choose_spec.2 d hd u v).symm

/-! ## Locality depends only on the law of `(h, D)` -/

section Law

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- joint locality of the (rescaled) internal metrics of `D` for a function of `h` only depends on
the law of `(h, D)` -/
theorem c18_jl_transfer {h : Ω → DistC} {D : Ω → ContMetric} {h' : Ω' → DistC}
    {E : Ω' → ContMetric} (hh : Measurable h) (hD : Measurable D) (hh' : Measurable h')
    (hE : Measurable E) (hlaw : P.map (fun ω => (h ω, D ω)) = P'.map (fun ω => (h' ω, E ω)))
    (hlD : ∀ᵐ ω ∂P, (D ω).IsLength) (hlE : ∀ᵐ ω ∂P', (E ω).IsLength) {f : DistC → DistC}
    (hf : Measurable f) {s : DistC → ℝ} (hs : Measurable s)
    (hI : IsJointlyLocalFam P (fun ω => f (h ω))
      (fun ω V u v => ENNReal.ofReal (s (h ω)) * (D ω).internal V u v)
      (fun ω V u v => ENNReal.ofReal (s (h ω)) * (D ω).internal V u v)) :
    IsJointlyLocalFam P' (fun ω => f (h' ω))
      (fun ω V u v => ENNReal.ofReal (s (h' ω)) * (E ω).internal V u v)
      (fun ω V u v => ENNReal.ofReal (s (h' ω)) * (E ω).internal V u v) := by
  let J : DistC × ContMetric → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
    fun t V u v => ENNReal.ofReal (s t.1) * c18J V t.2 u v
  have hJ : ∀ W : Set ℂ, IsOpen W → Measurable fun t => J t W := fun W hW =>
    measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v =>
      (ENNReal.measurable_ofReal.comp (hs.comp measurable_fst)).mul
        ((measurable_pi_apply v).comp ((measurable_pi_apply u).comp
          ((measurable_c18J hW).comp measurable_snd)))
  have e : ∀ {X : Type} [MeasurableSpace X] {Q : Measure X} {k : X → DistC} {F : X → ContMetric},
      (∀ᵐ x ∂Q, (F x).IsLength) → ∀ᵐ x ∂Q, ∀ V : Set ℂ, IsOpen V →
        J (k x, F x) V = fun u v => ENNReal.ofReal (s (k x)) * (F x).internal V u v :=
    fun hl => hl.mono fun x hx V hV => by
      funext u v
      simp only [J, c18J_eq hV hx]
  have h1 := isJointlyLocalFam_congr (J₁ := fun ω => J (h ω, D ω))
    (J₂ := fun ω => J (h ω, D ω)) hI (e hlD) (e hlD)
  have h2 := c18_isJointlyLocalFam_transfer (hh.prodMk hD) (hh'.prodMk hE) hlaw
    (g := fun t => f t.1) (hf.comp measurable_fst) hJ hJ h1
  exact isJointlyLocalFam_congr h2 ((e hlE).mono fun x hx V hV => (hx V hV).symm)
    ((e hlE).mono fun x hx V hV => (hx V hV).symm)

/-- the unscaled case of `c18_jl_transfer` -/
theorem c18_jl_transfer_plain {h : Ω → DistC} {D : Ω → ContMetric} {h' : Ω' → DistC}
    {E : Ω' → ContMetric} (hh : Measurable h) (hD : Measurable D) (hh' : Measurable h')
    (hE : Measurable E) (hlaw : P.map (fun ω => (h ω, D ω)) = P'.map (fun ω => (h' ω, E ω)))
    (hlD : ∀ᵐ ω ∂P, (D ω).IsLength) (hlE : ∀ᵐ ω ∂P', (E ω).IsLength)
    (hI : IsJointlyLocalFam P h (internalFam D) (internalFam D)) :
    IsJointlyLocalFam P' h' (internalFam E) (internalFam E) := by
  have e1 : ∀ {X : Type} [MeasurableSpace X] {Q : Measure X} {F : X → ContMetric},
      ∀ᵐ x ∂Q, ∀ V : Set ℂ, IsOpen V →
        (fun u v => ENNReal.ofReal 1 * (F x).internal V u v) =
          internalFam F x V :=
    Eventually.of_forall fun x V _ => by
      funext u v
      simp [internalFam]
  have H := c18_jl_transfer (f := id) (s := fun _ => 1) hh hD hh' hE hlaw hlD hlE measurable_id
    measurable_const (isJointlyLocalFam_congr hI e1 e1)
  exact isJointlyLocalFam_congr H (e1.mono fun x hx V hV => (hx V hV).symm)
    (e1.mono fun x hx V hV => (hx V hV).symm)

omit [IsProbabilityMeasure P] in
/-- LM Def 1.2 is LM Def 1.3 with `D₁ = D₂` -/
theorem c18_isLocalMetric_of_jl {h : Ω → DistC} {D : Ω → ContMetric} (hD : Measurable D)
    (hl : ∀ᵐ ω ∂P, (D ω).IsLength) (H : IsJointlyLocalFam P h (internalFam D) (internalFam D)) :
    IsLocalMetric P h D :=
  ⟨hD, hl, fun V => by simpa only [sup_idem, sup_assoc] using H V⟩

end Law

/-! ## Conditional independence given the field, with the field enlarged -/

theorem c18_condIndepEv_sup_cond {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G A B : MeasurableSpace Ω} (hG : G ≤ mΩ) (hA : A ≤ mΩ)
    (hB : B ≤ mΩ) (h : CondIndepEv G A B μ) : CondIndepEv G (A ⊔ G) (B ⊔ G) μ := by
  have h1 : CondIndepEv G B (A ⊔ G) μ :=
    condIndepEv_of_condExp_sup_eq hG hB (sup_le hA hG) fun b hb => by
      rw [sup_assoc, sup_idem]
      exact condExp_sup_eq_of_condIndepEv hG hA hB h hb
  exact condIndepEv_of_condExp_sup_eq hG (sup_le hA hG) (sup_le hB hG) fun a ha => by
    rw [sup_assoc, sup_idem]
    exact condExp_sup_eq_of_condIndepEv hG hB (sup_le hA hG) h1 ha

lemma c18_comap_le_of_factor {X β γ δ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    [mδ : MeasurableSpace δ] (k : X → β) (E : X → γ) {F : β × γ → δ} (hF : Measurable F) :
    mδ.comap (fun x => F (k x, E x)) ≤ mγ.comap E ⊔ mβ.comap k := by
  rw [show (fun x => F (k x, E x)) = F ∘ fun x => (k x, E x) from rfl,
    ← MeasurableSpace.comap_comp, sup_comm, ← MeasurableSpace.comap_prodMk]
  exact MeasurableSpace.comap_mono hF.comap_le

end LQGMetric.LM
