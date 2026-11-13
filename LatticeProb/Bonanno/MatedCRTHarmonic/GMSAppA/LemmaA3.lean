/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3FieldMom
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3Main

/-!
# [18] Lemma A.3: long-range independence for the whole-plane GFF

[18] = Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, arXiv 1807.07511v3, Lemma A.3
: "Let `N ∈ ℕ` and let `B_R(w)` be a ball which contains `𝔻`. Let
`h = (h¹, …, h^N)` be an `N`-tuple of i.i.d. whole-plane GFFs, each normalized so that its circle average over `∂B_R(w)`
is 0. … For `p₀ > p > 1` and `s ∈ (0,1)`, there are constants `a = a(p, p₀, N) > 0` and `b = b(p, p₀, s, N) > 0` (which do
not depend on `w, R`) such that for `δ ∈ (0, a]`, the following is true. Let `X` be a random variable which is a.s.
determined by `h|_{B_δ(0)}` and `h_1(0)`. Then
`E[|E[X | h|_{ℂ∖𝔻}] − E[X | h_1(0)]|^p] ≲ δ^{sp} E[|X|^p] + e^{−b/δ^{1−s}} E[|X|^{p₀}]^{p/p₀}` (A.6)
with implicit constant depending only on `p, p₀, s` and `N`."

This file proves the case `N = 1` (one whole-plane GFF; `N`-tuples need only the product of the Cameron–Martin
densities and of the energy moments, see the local interfaces), with `p ≥ 1`, explicit `a`, `b`, `C`, and "determined by" read
as `X = F(h|_{B_δ(0)}, h_1(0))` a.s. for a measurable `F`.

**Proof.** The paper's coupling `h̃` is realized on the product `P ⊗ P`: by the Markov decomposition
`h|_𝔻 = E + Z + C` (`DiskMarkov`, `FieldData`; `C = h_1(0)`, `E = 𝔥 − 𝔥(0)` independent of `C`, `Z` the
zero-boundary part independent of `σ(h|_{ℂ∖𝔻})`), `E[X | 𝒢]` and `E[X | σ(C)]` are integrals over `Z`, resp. over
`(E', Z)` (`lemmaA3_product`). The Radon–Nikodym derivative `M_δ` of Lemma A.5 is applied at each fixed `(ω, ω')`
(Cameron–Martin for the deterministic shift `φ_δ (𝔥_ω − 𝔥_{ω'})`, `cm_pointwise`), with energy bounded by the
measurable `MfG δ (ω, ω')`, whose exponential moment is bounded through Lemma A.4 (`lintegral_exp_MfG_le`); the
estimates (A.13)–(A.18) are then those of the paper.

* **`GMSAppA.lemmaA3`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-- the scale constant `A` of the tail exponent `q = A/δ` -/
def a3A (p p₀ : ℝ) : ℝ :=
  Real.sqrt (massQ ^ 2 / (200 * (25 * Real.pi * (|2 * cplExp p p₀ * (1 - 1 / p₀)| + 1) *
    (energyConst + 1)) * (logCovConst + 1)))

/-- the threshold `a` of [18] Lemma A.3 -/
def a3a (p p₀ : ℝ) : ℝ := min (1 / 20) (a3A p p₀ / max 1 (p₀ / (p₀ - 1)))

/-- the rate `b` of [18] Lemma A.3 -/
def a3b (p p₀ : ℝ) : ℝ := cplExp p p₀ * (1 - 1 / p₀) * (1 - p / p₀) * a3A p p₀ / 4

/-- the constant `C` of [18] Lemma A.3 -/
def a3C (p p₀ : ℝ) : ℝ :=
  2 ^ (p - 1) * 2 ^ (p - 1) * 2 * max 1 ((2 ^ cplExp p p₀ * 2) ^ (1 - p / p₀))

lemma a3A_pos (p p₀ : ℝ) : 0 < a3A p p₀ := by
  unfold a3A
  refine Real.sqrt_pos.2 (div_pos (pow_pos massQ_pos 2) ?_)
  have := energyConst_nonneg; have := logCovConst_nonneg
  positivity

section
variable {p p₀ s : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {R : ℝ} {w : ℂ}

/-- **[18] Lemma A.3 for a nonnegative functional**, with the tail constant of `lemmaA3_product`. -/
theorem lemmaA3_nonneg (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs0 : 0 < s)
    (hh : IsWholePlaneGFF h P) (hball : ball (0 : ℂ) 1 ⊆ ball w R)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) R w = 0) {δ : ℝ} (hδ0 : 0 < δ) (hδa : δ ≤ a3a p p₀)
    {X : Ω → ℝ} {Fn : DistOn (ballO 0 δ) × ℝ → ℝ} (hFn : Measurable Fn) (hFn0 : ∀ x, 0 ≤ Fn x)
    (hX : X =ᵐ[P] fun ω => Fn (restrictTo (ballO 0 δ) (h ω), circleAvg (h ω) 1 0))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal (X ω) ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal |P[X | extSigma h] ω -
        P[X | MeasurableSpace.comap (fun ω => circleAvg (h ω) 1 0) inferInstance] ω| ^ p ∂P ≤
      2 ^ (p - 1) * (ENNReal.ofReal (δ ^ s) ^ p * ∫⁻ ω, ENNReal.ofReal (X ω) ^ p ∂P +
        (∫⁻ ω, ENNReal.ofReal (X ω) ^ p₀ ∂P) ^ (p / p₀) *
          ENNReal.ofReal (cplTail p p₀ (a3A p p₀ / δ) (δ ^ s) 2) ^ (1 - p / p₀)) := by
  have hp0 : 0 < p := by linarith
  have hp₀1 : 1 < p₀ := by linarith
  have hp₀ : 0 < p₀ := by linarith
  -- the geometry
  have hR : 0 < R := by
    have h0 : (0 : ℂ) ∈ ball w R := hball (mem_ball_self one_pos)
    exact (dist_nonneg).trans_lt h0
  have hdisj : Disjoint (ball (0 : ℂ) 1) (sphere w R) :=
    Set.disjoint_left.2 fun x hx hx' => by
      have := hball hx
      rw [mem_ball] at this; rw [mem_sphere] at hx'; linarith
  have hnest : closedBall (0 : ℂ) 1 ⊆ closedBall w R := by
    rw [← closure_ball (0 : ℂ) one_ne_zero, ← closure_ball w hR.ne']
    exact closure_mono hball
  obtain ⟨M⟩ := exists_diskMarkov hh hR hn hdisj
  have hm : extSigma h ≤ ‹MeasurableSpace Ω› := extSigma_le hh.measurable
  -- parameters
  set A := a3A p p₀ with hA
  have hA0 : 0 < A := a3A_pos p p₀
  set r₀ := p₀ / (p₀ - 1) with hr₀
  have hδ20 : δ ≤ 1 / 20 := hδa.trans (min_le_left _ _)
  have hδ10 : δ < 1 / 10 := by linarith
  have hδA : δ ≤ A / max 1 r₀ := hδa.trans (min_le_right _ _)
  have hmax : 0 < max 1 r₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  set q := A / δ with hq
  have hqmax : max 1 r₀ ≤ q := by
    rw [hq, le_div_iff₀ hδ0]
    rw [le_div_iff₀ hmax] at hδA
    linarith
  have hq1 : 1 ≤ q := (le_max_left _ _).trans hqmax
  have hqr : r₀ ≤ q := (le_max_right _ _).trans hqmax
  set t := δ ^ s with ht
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hδ0 s).le
  have ht1 : t < 1 := Real.rpow_lt_one hδ0.le (by linarith) hs0
  set sc := cplExp p p₀ with hsc
  set θ := 1 - 1 / p₀ with hθ
  set κ := 2 * sc * θ * q ^ 2 with hκdef
  have hsc0 : 0 ≤ sc := by
    rw [hsc, cplExp]; exact mul_nonneg hp0.le (div_nonneg hp₀.le (by linarith))
  have hθ0 : 0 ≤ θ := by rw [hθ, sub_nonneg, div_le_one hp₀]; exact hp₀1.le
  have hκ0 : 0 ≤ κ := by positivity
  have hκ : 200 * (25 * Real.pi * κ * energyConst) * logCovConst * δ ^ 2 ≤ massQ ^ 2 := by
    have hE0 := energyConst_nonneg
    have hL0 := logCovConst_nonneg
    have hA2 : A ^ 2 = massQ ^ 2 / (200 * (25 * Real.pi * (|2 * sc * θ| + 1) *
        (energyConst + 1)) * (logCovConst + 1)) := by
      rw [hA, a3A, Real.sq_sqrt (by positivity)]
    have hκδ : κ * δ ^ 2 = 2 * sc * θ * A ^ 2 := by
      rw [hκdef, hq]; field_simp
    have hden : 0 < 200 * (25 * Real.pi * (|2 * sc * θ| + 1) * (energyConst + 1)) *
        (logCovConst + 1) := by positivity
    calc 200 * (25 * Real.pi * κ * energyConst) * logCovConst * δ ^ 2
        = 200 * 25 * Real.pi * energyConst * logCovConst * (κ * δ ^ 2) := by ring
      _ = 200 * 25 * Real.pi * (2 * sc * θ) * energyConst * logCovConst * A ^ 2 := by
          rw [hκδ]; ring
      _ ≤ 200 * 25 * Real.pi * (|2 * sc * θ| + 1) * (energyConst + 1) * (logCovConst + 1) *
          A ^ 2 := by
          have h1 : 2 * sc * θ ≤ |2 * sc * θ| + 1 := (le_abs_self _).trans (by linarith)
          gcongr
          · linarith
          · linarith
      _ = massQ ^ 2 := by rw [hA2]; field_simp
  -- the data
  set E := M.Ed
  set C := DiskMarkov.cAvg h
  set Z := M.Zd
  obtain ⟨hCEZ, hEZ⟩ := M.indepFun_cAvg_EdZd hh hR hnest hn
  set Φ : DistOn (ballO 0 1) × ℝ × DistOn (ballO 0 1) → ℝ := fun x =>
    Fn (resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (x.1 + x.2.2) x.2.1), x.2.1)
    with hΦdef
  have hΦm : Measurable Φ :=
    hFn.comp ((DiskMarkov.measurable_fieldOf δ).prodMk (measurable_fst.comp measurable_snd))
  have hBsub : ballO (0 : ℂ) δ ≤ ballO 0 1 := fun z hz => by
    show z ∈ ball (0 : ℂ) 1
    have : z ∈ ball (0 : ℂ) δ := hz
    rw [mem_ball, dist_zero_right] at this ⊢; linarith
  have hXΦ : X =ᵐ[P] fun ω => Φ (E ω, C ω, Z ω) := by
    filter_upwards [hX, M.restrictTo_eq] with ω h1 h2
    rw [h1]
    simp only [hΦdef]
    rw [← resOn_restrictTo hBsub, h2]
    rfl
  have hCM := M.cm_pointwise hh hδ0 hδ10
  have hCM' : ∀ᵐ x ∂(P.prod P), ∃ ρ : DistOn (ballO 0 1) → ℝ, Measurable ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      ∃ V : ℝ, 0 ≤ V ∧ V ≤ M.MfG δ x ∧
        (∀ s : ℝ, ∫⁻ z, ENNReal.ofReal (ρ z) ^ s ∂(P.map Z) =
          ENNReal.ofReal (Real.exp (s * (s - 1) * V / 2))) ∧
        ∀ c : ℝ, ∫⁻ z, ENNReal.ofReal (Φ (E x.1, c, z)) ∂(P.map Z) =
          ∫⁻ z, ENNReal.ofReal (Φ (E x.2, c, z)) * ENNReal.ofReal (ρ z) ∂(P.map Z) := by
    filter_upwards [hCM] with x ⟨ρ, hρm, hρ0, V, hV0, hVM, hmom, hshift⟩
    exact ⟨ρ, hρm, hρ0, V, hV0, hVM, hmom, fun c => hshift Fn hFn c⟩
  have hmom := M.lintegral_exp_MfG_le hh hδ0 hδ10 hκ0 hκ
  have hres := lemmaA3_product (P := P) (𝓖 := extSigma h) hm M.measurable_Ed_ext
    (DiskMarkov.measurable_cAvg_ext h) M.measurable_Zd M.indep_ext_Zd hCEZ hEZ hΦm
    (fun x => hFn0 _) hXΦ hp hpp₀ hq1 hqr ht0 ht1 (M.measurable_MfG hh.measurable δ) hCM'
    hmom hXp₀
  exact hres

/-- the σ-algebra `σ(h_1(0))` -/
def cSigma {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => circleAvg (h ω) 1 0) inferInstance

/-- the tail factor of `lemmaA3_nonneg` in closed form -/
lemma cplTail_rpow_eq (hp : 1 ≤ p) (hpp₀ : p < p₀) {δ : ℝ} (hδ0 : 0 < δ) :
    ENNReal.ofReal (cplTail p p₀ (a3A p p₀ / δ) (δ ^ s) 2) ^ (1 - p / p₀) =
      ENNReal.ofReal ((2 ^ cplExp p p₀ * 2) ^ (1 - p / p₀)) *
        ENNReal.ofReal (Real.exp (-(a3b p p₀ / δ ^ (1 - s)))) := by
  have hp₀ : 0 < p₀ := by linarith
  have hθp : 0 ≤ 1 - p / p₀ := by rw [sub_nonneg, div_le_one hp₀]; exact hpp₀.le
  have hct : 0 ≤ cplTail p p₀ (a3A p p₀ / δ) (δ ^ s) 2 := by
    unfold cplTail; positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hct hθp, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold cplTail
  rw [show 2 ^ cplExp p p₀ * Real.exp (-(cplExp p p₀ * (1 - 1 / p₀) *
      (a3A p p₀ / δ * δ ^ s / 4))) * 2 = (2 ^ cplExp p p₀ * 2) *
      Real.exp (-(cplExp p p₀ * (1 - 1 / p₀) * (a3A p p₀ / δ * δ ^ s / 4))) by ring,
    Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  rw [a3b, Real.rpow_sub hδ0, Real.rpow_one]
  field_simp

/-- **[18] Lemma A.3** (`N = 1`, `p ≥ 1`): for a whole-plane GFF `h` normalized so that `h_R(w) = 0` with
`𝔻 ⊆ B_R(w)`, `δ ∈ (0, a]` and `X = F(h|_{B_δ(0)}, h_1(0))`,
`E|E[X | σ(h|_{ℂ∖𝔻})] − E[X | h_1(0)]|^p ≤ C (δ^{sp} E|X|^p + e^{−b/δ^{1−s}} E[|X|^{p₀}]^{p/p₀})`
with `a = a3a p p₀`, `b = a3b p p₀`, `C = a3C p p₀` (independent of `w`, `R`, `δ`, `X`). -/
theorem lemmaA3 (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs0 : 0 < s)
    (hh : IsWholePlaneGFF h P) (hball : ball (0 : ℂ) 1 ⊆ ball w R)
    (hn : ∀ᵐ ω ∂P, circleAvg (h ω) R w = 0) {δ : ℝ} (hδ0 : 0 < δ) (hδa : δ ≤ a3a p p₀)
    {X : Ω → ℝ} {F : DistOn (ballO 0 δ) × ℝ → ℝ} (hF : Measurable F)
    (hX : X =ᵐ[P] fun ω => F (restrictTo (ballO 0 δ) (h ω), circleAvg (h ω) 1 0))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal |P[X | extSigma h] ω -
        P[X | MeasurableSpace.comap (fun ω => circleAvg (h ω) 1 0) inferInstance] ω| ^ p ∂P ≤
      ENNReal.ofReal (a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) * ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P +
          ENNReal.ofReal (Real.exp (-(a3b p p₀ / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P) ^ (p / p₀)) := by
  have hp0 : 0 < p := by linarith
  have hp₀1 : 1 < p₀ := by linarith
  have hp₀ : 0 < p₀ := by linarith
  show ∫⁻ ω, ENNReal.ofReal |P[X | extSigma h] ω - P[X | cSigma h] ω| ^ p ∂P ≤ _
  -- positive and negative parts
  set Xp : Ω → ℝ := fun ω => max (X ω) 0
  set Xn : Ω → ℝ := fun ω => max (-X ω) 0
  have hFp : Measurable fun x => max (F x) 0 := hF.max measurable_const
  have hFn : Measurable fun x => max (-F x) 0 := hF.neg.max measurable_const
  have hXp : Xp =ᵐ[P] fun ω => max (F (restrictTo (ballO 0 δ) (h ω), circleAvg (h ω) 1 0)) 0 := by
    filter_upwards [hX] with ω hω; simp only [Xp, hω]
  have hXn : Xn =ᵐ[P] fun ω => max (-F (restrictTo (ballO 0 δ) (h ω), circleAvg (h ω) 1 0)) 0 := by
    filter_upwards [hX] with ω hω; simp only [Xn, hω]
  have hle : ∀ (ω : Ω) (r : ℝ), 0 ≤ r → ENNReal.ofReal (Xp ω) ^ r ≤ ENNReal.ofReal |X ω| ^ r ∧
      ENNReal.ofReal (Xn ω) ^ r ≤ ENNReal.ofReal |X ω| ^ r := by
    intro ω r hr
    constructor <;> refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hr
    · exact max_le (le_abs_self _) (abs_nonneg _)
    · exact max_le (neg_le_abs _) (abs_nonneg _)
  have hXpp₀ : ∫⁻ ω, ENNReal.ofReal (Xp ω) ^ p₀ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hXp₀ (lintegral_mono fun ω => (hle ω p₀ hp₀.le).1)
  have hXnp₀ : ∫⁻ ω, ENNReal.ofReal (Xn ω) ^ p₀ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hXp₀ (lintegral_mono fun ω => (hle ω p₀ hp₀.le).2)
  have hresP := lemmaA3_nonneg (s := s) hp hpp₀ hs0 hh hball hn hδ0 hδa hFp
    (fun x => le_max_right _ _) hXp hXpp₀
  have hresN := lemmaA3_nonneg (s := s) hp hpp₀ hs0 hh hball hn hδ0 hδa hFn
    (fun x => le_max_right _ _) hXn hXnp₀
  -- integrability of `X`
  have hXae : AEStronglyMeasurable X P := by
    refine (AEStronglyMeasurable.congr ?_ hX.symm)
    exact (hF.comp (((measurable_restrictTo _).comp hh.measurable).prodMk
      ((measurable_circleAvg_left 1 0).comp hh.measurable))).aestronglyMeasurable
  have hXi : Integrable X P := by
    refine ⟨hXae, ?_⟩
    rw [HasFiniteIntegral]
    have h1 := lintegral_rpow_le_rpow_lintegral (P := P) (Z := fun ω => ENNReal.ofReal |X ω|)
      (continuous_abs.measurable.comp_aemeasurable hXae.aemeasurable).ennreal_ofReal one_pos hp₀1.le
    simp only [ENNReal.rpow_one] at h1
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hXp₀) h1))
    exact le_of_eq (lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal_abs])
  have hXpi : Integrable Xp P := hXi.pos_part
  have hXni : Integrable Xn P := hXi.neg_part
  have hXsplit : X = fun ω => Xp ω - Xn ω := by
    funext ω; simp only [Xp, Xn]; exact (max_zero_sub_max_neg_zero_eq_self (X ω)).symm
  have hcG : P[X | (extSigma h)] =ᵐ[P] fun ω => P[Xp | (extSigma h)] ω - P[Xn | (extSigma h)] ω := by
    conv_lhs => rw [hXsplit]
    exact condExp_sub hXpi hXni (extSigma h)
  have hcH : P[X | (cSigma h)] =ᵐ[P] fun ω => P[Xp | (cSigma h)] ω - P[Xn | (cSigma h)] ω := by
    conv_lhs => rw [hXsplit]
    exact condExp_sub hXpi hXni (cSigma h)
  -- combine
  set Dp : Ω → ℝ := fun ω => P[Xp | (extSigma h)] ω - P[Xp | (cSigma h)] ω
  set Dn : Ω → ℝ := fun ω => P[Xn | (extSigma h)] ω - P[Xn | (cSigma h)] ω
  have hGle : extSigma h ≤ ‹MeasurableSpace Ω› := extSigma_le hh.measurable
  have hHle : cSigma h ≤ ‹MeasurableSpace Ω› :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).comap_le
  have hmG : ∀ f : Ω → ℝ, Measurable (P[f | extSigma h]) := fun f =>
    (stronglyMeasurable_condExp.mono hGle).measurable
  have hmH : ∀ f : Ω → ℝ, Measurable (P[f | cSigma h]) := fun f =>
    (stronglyMeasurable_condExp.mono hHle).measurable
  have hmeasD : AEMeasurable (fun ω => ENNReal.ofReal |Dp ω| ^ p) P ∧
      AEMeasurable (fun ω => ENNReal.ofReal |Dn ω| ^ p) P :=
    ⟨((continuous_abs.measurable.comp ((hmG Xp).sub (hmH Xp))).ennreal_ofReal.pow_const p).aemeasurable,
      ((continuous_abs.measurable.comp ((hmG Xn).sub (hmH Xn))).ennreal_ofReal.pow_const p).aemeasurable⟩
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |P[X | (extSigma h)] ω - P[X | (cSigma h)] ω| ^ p ≤
      2 ^ (p - 1) * (ENNReal.ofReal |Dp ω| ^ p + ENNReal.ofReal |Dn ω| ^ p) := by
    filter_upwards [hcG, hcH] with ω h1 h2
    rw [h1, h2]
    calc ENNReal.ofReal |P[Xp | (extSigma h)] ω - P[Xn | (extSigma h)] ω - (P[Xp | (cSigma h)] ω - P[Xn | (cSigma h)] ω)| ^ p
        ≤ (ENNReal.ofReal |Dp ω| + ENNReal.ofReal |Dn ω|) ^ p := by
          refine ENNReal.rpow_le_rpow ?_ hp0.le
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : P[Xp | (extSigma h)] ω - P[Xn | (extSigma h)] ω - (P[Xp | (cSigma h)] ω - P[Xn | (cSigma h)] ω) = Dp ω - Dn ω := by
            simp only [Dp, Dn]; ring
          rw [this]
          exact abs_sub _ _
      _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
  set Ip := ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P
  set Ip₀ := ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P
  set T := ENNReal.ofReal (cplTail p p₀ (a3A p p₀ / δ) (δ ^ s) 2) ^ (1 - p / p₀)
  have hθp : 0 ≤ p / p₀ := div_nonneg hp0.le hp₀.le
  have hbnd : ∀ (Y : Ω → ℝ), (∀ (ω : Ω) (r : ℝ), 0 ≤ r →
      ENNReal.ofReal (Y ω) ^ r ≤ ENNReal.ofReal |X ω| ^ r) →
      2 ^ (p - 1) * (ENNReal.ofReal (δ ^ s) ^ p * ∫⁻ ω, ENNReal.ofReal (Y ω) ^ p ∂P +
        (∫⁻ ω, ENNReal.ofReal (Y ω) ^ p₀ ∂P) ^ (p / p₀) * T) ≤
      2 ^ (p - 1) * (ENNReal.ofReal (δ ^ s) ^ p * Ip + Ip₀ ^ (p / p₀) * T) := by
    intro Y hY
    gcongr
    · exact lintegral_mono fun ω => hY ω p hp0.le
    · exact lintegral_mono fun ω => hY ω p₀ hp₀.le
  have hP' := hresP.trans (hbnd Xp fun ω r hr => (hle ω r hr).1)
  have hN' := hresN.trans (hbnd Xn fun ω r hr => (hle ω r hr).2)
  have hT : T = ENNReal.ofReal (((2 : ℝ) ^ cplExp p p₀ * 2) ^ (1 - p / p₀)) *
      ENNReal.ofReal (Real.exp (-(a3b p p₀ / δ ^ (1 - s)))) := cplTail_rpow_eq hp hpp₀ hδ0
  set C₁ : ℝ := ((2 : ℝ) ^ cplExp p p₀ * 2) ^ (1 - p / p₀)
  have hC₁ : 0 ≤ C₁ := by positivity
  have hδsp : ENNReal.ofReal (δ ^ s) ^ p = ENNReal.ofReal (δ ^ (s * p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_pos_of_pos hδ0 s).le hp0.le, ← Real.rpow_mul hδ0.le]
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]; norm_num
  calc ∫⁻ ω, ENNReal.ofReal |P[X | (extSigma h)] ω - P[X | (cSigma h)] ω| ^ p ∂P
      ≤ ∫⁻ ω, 2 ^ (p - 1) * (ENNReal.ofReal |Dp ω| ^ p + ENNReal.ofReal |Dn ω| ^ p) ∂P :=
        lintegral_mono_ae hpt
    _ = 2 ^ (p - 1) * (∫⁻ ω, ENNReal.ofReal |Dp ω| ^ p ∂P + ∫⁻ ω, ENNReal.ofReal |Dn ω| ^ p ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
          lintegral_add_left' hmeasD.1]
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (ENNReal.ofReal (δ ^ s) ^ p * Ip + Ip₀ ^ (p / p₀) * T) +
          2 ^ (p - 1) * (ENNReal.ofReal (δ ^ s) ^ p * Ip + Ip₀ ^ (p / p₀) * T)) :=
        mul_le_mul' le_rfl (add_le_add hP' hN')
    _ = ENNReal.ofReal (2 ^ (p - 1) * 2 ^ (p - 1) * 2) *
          (ENNReal.ofReal (δ ^ (s * p)) * Ip + ENNReal.ofReal C₁ *
            (ENNReal.ofReal (Real.exp (-(a3b p p₀ / δ ^ (1 - s)))) * Ip₀ ^ (p / p₀))) := by
        rw [hT, hδsp, h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (2 ^ (p - 1) * 2 ^ (p - 1) * 2) *
          (ENNReal.ofReal (max 1 C₁) * (ENNReal.ofReal (δ ^ (s * p)) * Ip) +
            ENNReal.ofReal (max 1 C₁) *
              (ENNReal.ofReal (Real.exp (-(a3b p p₀ / δ ^ (1 - s)))) * Ip₀ ^ (p / p₀))) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · calc ENNReal.ofReal (δ ^ (s * p)) * Ip = 1 * (ENNReal.ofReal (δ ^ (s * p)) * Ip) :=
                (one_mul _).symm
            _ ≤ ENNReal.ofReal (max 1 C₁) * (ENNReal.ofReal (δ ^ (s * p)) * Ip) := by
                refine mul_le_mul' ?_ le_rfl
                rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
        · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
    _ = ENNReal.ofReal (a3C p p₀) *
          (ENNReal.ofReal (δ ^ (s * p)) * Ip +
            ENNReal.ofReal (Real.exp (-(a3b p p₀ / δ ^ (1 - s)))) * Ip₀ ^ (p / p₀)) := by
        rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), a3C]

end

end MatedCRTHarmonic.GMSAppA
