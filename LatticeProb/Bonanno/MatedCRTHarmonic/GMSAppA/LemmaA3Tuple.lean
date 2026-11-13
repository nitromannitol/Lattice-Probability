/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3Tuple at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3Signed
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.TupleCM
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.TupleIndep

/-!
# [18] Lemma A.3 for an `N`-tuple of independent whole-plane GFFs

[18] (GMS, arXiv 1807.07511v3) Lemma A.3 : "Let `N ∈ ℕ` and let
`B_R(w)` be a ball which contains `𝔻`. Let `h = (h¹, …, h^N)` be an `N`-tuple of i.i.d. whole-plane GFFs, each
normalized so that its circle average over `∂B_R(w)` is 0. … there are constants `a = a(p, p₀, N) > 0` and
`b = b(p, p₀, s, N) > 0` (which do not depend on `w, R`) such that for `δ ∈ (0, a]` … Let `X` be a random variable which
is a.s. determined by `h|_{B_δ(0)}` and `h_1(0)`. Then
`E[|E[X | h|_{ℂ∖𝔻}] − E[X | h_1(0)]|^p] ≲ δ^{sp} E[|X|^p] + e^{−b/δ^{1−s}} E[|X|^{p₀}]^{p/p₀}` (A.6)."

Here `h : ι → Ω → DistC` with `ι` finite, `N = |ι|`, independence is `iIndepFun h P` (identical distribution is not
needed), `σ(h|_{ℂ∖𝔻}) = ⨆_k σ(h^k|_{ℂ∖𝔻})` (`extSigmaN`), `σ(h_1(0)) = σ((h^k_1(0))_k)` (`cSigmaN`), and "determined
by" is read as `X = F((h^k|_{B_δ(0)})_k, (h^k_1(0))_k)` a.s. for a measurable `F`. The constants are explicit:
`a = a3aN p p₀ N` (the one-field `a3a p p₀` divided, inside, by `√N`), `b = a3bN p p₀ N`, and the implicit constant
`a3C p p₀` of the one-field case (independent of `N`).

**Proof.** As for one field (`lemmaA3`), with the data `E = (E^k)_k`, `C = (C^k)_k`, `Z = (Z^k)_k` of the `N` Markov
decompositions, taken with `σ(h^k)`-measurable zero-boundary parts (`exists_diskMarkov_meas`) so that the per-field
independences combine across fields (`indep_iSup_iSup_of_iIndep`). The law of `Z` is the product of the laws of the
`Z^k`; the change of measure is the product of the `N` one-field Cameron–Martin densities (`cm_shift`,
`lintegral_pi_shift`) with variance `∑_k V_k ≤ ∑_k MfG_k`, and the exponential moment of `∑_k MfG_k` is bounded by
Hölder's inequality from the one-field moment bound at `N κ` (`lintegral_exp_MfG_le`).

* `GMSAppA.indep_dataN` — the independence structure of the tuple data `(E, C, Z)`.
* `GMSAppA.cm_pointwiseN` — the product change of measure.
* `GMSAppA.lintegral_exp_MfN_le` — the exponential moment of the energy bound.
* `GMSAppA.lemmaA3N_nonneg` — nonnegative functionals.
* **`GMSAppA.lemmaA3N`** — [18] Lemma A.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

/-- `σ(h|_{ℂ∖𝔻})` for a tuple of fields -/
@[reducible] def extSigmaN {ι Ω : Type} [MeasurableSpace Ω] (h : ι → Ω → DistC) : MeasurableSpace Ω :=
  ⨆ k, extSigma (h k)

/-- `σ(h_1(0))` for a tuple of fields -/
@[reducible] def cSigmaN {ι Ω : Type} [MeasurableSpace Ω] (h : ι → Ω → DistC) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω k => circleAvg (h k ω) 1 0) inferInstance

/-- the observation `((h^k|_{B_δ(0)})_k, (h^k_1(0))_k)` -/
def obsN {ι Ω : Type} (δ : ℝ) (h : ι → Ω → DistC) (ω : Ω) :
    (ι → DistOn (ballO 0 δ)) × (ι → ℝ) :=
  (fun k => restrictTo (ballO 0 δ) (h k ω), fun k => circleAvg (h k ω) 1 0)

lemma measurable_obsN {ι Ω : Type} [MeasurableSpace Ω] (δ : ℝ) {h : ι → Ω → DistC}
    (hh : ∀ k, Measurable (h k)) : Measurable (obsN δ h) :=
  (measurable_pi_iff.2 fun k => (measurable_restrictTo _).comp (hh k)).prodMk
    (measurable_pi_iff.2 fun k => (measurable_circleAvg_left 1 0).comp (hh k))

/-- measurability into a product, w.r.t. an arbitrary σ-algebra on the domain -/
lemma measurable_pi_of {α ι : Type*} {m : MeasurableSpace α} {X : ι → Type*}
    [∀ a, MeasurableSpace (X a)] {g : α → ∀ a, X a} (hg : ∀ a, Measurable[m] fun x => g x a) :
    Measurable[m] g :=
  measurable_pi_iff.2 hg

/-- the scale constant `A_N = A/√N` -/
def a3AN (p p₀ : ℝ) (N : ℕ) : ℝ := a3A p p₀ / Real.sqrt N

/-- the threshold `a = a(p, p₀, N)` of [18] Lemma A.3 -/
def a3aN (p p₀ : ℝ) (N : ℕ) : ℝ := min (1 / 20) (a3AN p p₀ N / max 1 (p₀ / (p₀ - 1)))

/-- the rate `b = b(p, p₀, N)` of [18] Lemma A.3 -/
def a3bN (p p₀ : ℝ) (N : ℕ) : ℝ := cplExp p p₀ * (1 - 1 / p₀) * (1 - p / p₀) * a3AN p p₀ N / 4

section
variable {ι : Type} [Fintype ι] {p p₀ s : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : ι → Ω → DistC} {R : ℝ} {w : ℂ}

/-- the tuple `E = (E^k)_k` of harmonic parts minus centre values -/
def EdN (M : ∀ k, DiskMarkov P (h k)) (ω : Ω) : ι → DistOn (ballO 0 1) := fun k => (M k).Ed ω

/-- the tuple `Z = (Z^k)_k` of zero-boundary parts -/
def ZdN (M : ∀ k, DiskMarkov P (h k)) (ω : Ω) : ι → DistOn (ballO 0 1) := fun k => (M k).Zd ω

/-- the tuple `C = (h^k_1(0))_k` -/
def cAvgN (h : ι → Ω → DistC) (ω : Ω) : ι → ℝ := fun k => DiskMarkov.cAvg (h k) ω

/-- the energy bound `∑_k MfG_k` -/
def MfN (M : ∀ k, DiskMarkov P (h k)) (δ : ℝ) (x : Ω × Ω) : ℝ := ∑ k, (M k).MfG δ x

/-- the functional `(e, c, z) ↦ Fn(((e_k + z_k + c_k)|_{B_δ})_k, c)` -/
def PhiN (δ : ℝ) (Fn : (ι → DistOn (ballO 0 δ)) × (ι → ℝ) → ℝ)
    (x : (ι → DistOn (ballO 0 1)) × (ι → ℝ) × (ι → DistOn (ballO 0 1))) : ℝ :=
  Fn (fun k => resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (x.1 k + x.2.2 k) (x.2.1 k)),
    x.2.1)

omit [Fintype ι] in
lemma measurable_PhiN (δ : ℝ) {Fn : (ι → DistOn (ballO 0 δ)) × (ι → ℝ) → ℝ} (hFn : Measurable Fn) :
    Measurable (PhiN δ Fn) := by
  have hg : ∀ k, Measurable fun y : (ι → DistOn (ballO 0 1)) × (ι → ℝ) ×
      (ι → DistOn (ballO 0 1)) => (y.1 k, y.2.1 k, y.2.2 k) := fun k =>
    ((measurable_pi_apply k).comp measurable_fst).prodMk
      (((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)))
  have hcomp : ∀ k, Measurable fun y : (ι → DistOn (ballO 0 1)) × (ι → ℝ) ×
      (ι → DistOn (ballO 0 1)) =>
        resOn (ballO 0 δ) (ballO 0 1) (addConstOn (ballO 0 1) (y.1 k + y.2.2 k) (y.2.1 k)) :=
    fun k => by
      have H := (DiskMarkov.measurable_fieldOf δ).comp (hg k)
      exact H
  have H := hFn.comp ((measurable_pi_iff.2 hcomp).prodMk (measurable_fst.comp measurable_snd))
  exact H

/-- **Independence structure of the tuple data.** -/
theorem indep_dataN (hh : ∀ k, IsWholePlaneGFF (h k) P) (hind : iIndepFun h P)
    (M : ∀ k, DiskMarkov P (h k))
    (hMz : ∀ k, Measurable[MeasurableSpace.comap (h k) inferInstance] (M k).hz)
    (hR : 0 < R) (hnest : closedBall (0 : ℂ) 1 ⊆ closedBall w R)
    (hn : ∀ k, ∀ᵐ ω ∂P, circleAvg (h k ω) R w = 0) :
    Indep (extSigmaN h) (MeasurableSpace.comap (ZdN M) inferInstance) P ∧
      IndepFun (cAvgN h) (fun ω => (EdN M ω, ZdN M ω)) P ∧ IndepFun (EdN M) (ZdN M) P ∧
      P.map (ZdN M) = Measure.pi fun k => P.map (M k).Zd := by
  have h𝒜 : iIndep (fun k => MeasurableSpace.comap (h k) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).1 hind
  have h𝒜le : ∀ k, MeasurableSpace.comap (h k) inferInstance ≤ ‹MeasurableSpace Ω› :=
    fun k => (hh k).measurable.comap_le
  have hZk : ∀ k, MeasurableSpace.comap (M k).Zd inferInstance ≤
      MeasurableSpace.comap (h k) inferInstance :=
    fun k => ((M k).measurable_Zd_comap (hMz k)).comap_le
  have hEk : ∀ k, MeasurableSpace.comap (M k).Ed inferInstance ≤
      MeasurableSpace.comap (h k) inferInstance :=
    fun k => DiskMarkov.measurable_Ed_comap.comap_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H := indep_iSup_iSup_of_iIndep h𝒜 (B := fun k => extSigma (h k))
      (D := fun k => MeasurableSpace.comap (M k).Zd inferInstance)
      (fun k => extSigma_le_comap (h k)) hZk h𝒜le (fun k => (M k).indep_ext_Zd)
    refine indep_of_indep_of_le_right H ?_
    exact (measurable_pi_of fun k => (comap_measurable (M k).Zd).mono
      (le_iSup (fun k => MeasurableSpace.comap (M k).Zd inferInstance) k) le_rfl).comap_le
  · have H := indep_iSup_iSup_of_iIndep h𝒜
      (B := fun k => MeasurableSpace.comap (DiskMarkov.cAvg (h k)) inferInstance)
      (D := fun k => MeasurableSpace.comap (fun ω => ((M k).Ed ω, (M k).Zd ω)) inferInstance)
      (fun k => DiskMarkov.measurable_cAvg_comap.comap_le)
      (fun k => (DiskMarkov.measurable_Ed_comap.prodMk
        ((M k).measurable_Zd_comap (hMz k))).comap_le) h𝒜le
      (fun k => (IndepFun_iff_Indep _ _ _).1 ((M k).indepFun_cAvg_EdZd (hh k) hR hnest (hn k)).1)
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left H ?_) ?_
    · exact (measurable_pi_of fun k => (comap_measurable (DiskMarkov.cAvg (h k))).mono
        (le_iSup (fun k => MeasurableSpace.comap (DiskMarkov.cAvg (h k)) inferInstance) k)
          le_rfl).comap_le
    · refine Measurable.comap_le (Measurable.prodMk ?_ ?_)
      · exact measurable_pi_of fun k => (measurable_fst.comp
          (comap_measurable (fun ω => ((M k).Ed ω, (M k).Zd ω)))).mono
          (le_iSup (fun k => MeasurableSpace.comap (fun ω => ((M k).Ed ω, (M k).Zd ω))
            inferInstance) k) le_rfl
      · exact measurable_pi_of fun k => (measurable_snd.comp
          (comap_measurable (fun ω => ((M k).Ed ω, (M k).Zd ω)))).mono
          (le_iSup (fun k => MeasurableSpace.comap (fun ω => ((M k).Ed ω, (M k).Zd ω))
            inferInstance) k) le_rfl
  · have H := indep_iSup_iSup_of_iIndep h𝒜
      (B := fun k => MeasurableSpace.comap (M k).Ed inferInstance)
      (D := fun k => MeasurableSpace.comap (M k).Zd inferInstance) hEk hZk h𝒜le
      (fun k => (IndepFun_iff_Indep _ _ _).1 ((M k).indepFun_cAvg_EdZd (hh k) hR hnest (hn k)).2)
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left H ?_) ?_
    · exact (measurable_pi_of fun k => (comap_measurable (M k).Ed).mono
        (le_iSup (fun k => MeasurableSpace.comap (M k).Ed inferInstance) k) le_rfl).comap_le
    · exact (measurable_pi_of fun k => (comap_measurable (M k).Zd).mono
        (le_iSup (fun k => MeasurableSpace.comap (M k).Zd inferInstance) k) le_rfl).comap_le
  · have hZind : iIndepFun (fun k => (M k).Zd) P := by
      rw [iIndepFun_iff_iIndep]
      exact iIndep_of_iIndep_of_le h𝒜 hZk
    exact (iIndepFun_iff_map_fun_eq_pi_map fun k => (M k).measurable_Zd.aemeasurable).1 hZind

/-- **The pointwise change of measure for the tuple**: the product of the `N` one-field Cameron–Martin densities. -/
theorem cm_pointwiseN (hh : ∀ k, IsWholePlaneGFF (h k) P) (M : ∀ k, DiskMarkov P (h k))
    (hZmap : P.map (ZdN M) = Measure.pi fun k => P.map (M k).Zd) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ10 : δ < 1 / 10) {Fn : (ι → DistOn (ballO 0 δ)) × (ι → ℝ) → ℝ} (hFn : Measurable Fn) :
    ∀ᵐ x ∂(P.prod P), ∃ ρ : (ι → DistOn (ballO 0 1)) → ℝ, Measurable ρ ∧
      (∀ z, 0 ≤ ρ z) ∧ ∃ V : ℝ, 0 ≤ V ∧ V ≤ MfN M δ x ∧
        (∀ s : ℝ, ∫⁻ z, ENNReal.ofReal (ρ z) ^ s ∂(P.map (ZdN M)) =
          ENNReal.ofReal (Real.exp (s * (s - 1) * V / 2))) ∧
        ∀ c : ι → ℝ, ∫⁻ z, ENNReal.ofReal (PhiN δ Fn (EdN M x.1, c, z)) ∂(P.map (ZdN M)) =
          ∫⁻ z, ENNReal.ofReal (PhiN δ Fn (EdN M x.2, c, z)) * ENNReal.ofReal (ρ z)
            ∂(P.map (ZdN M)) := by
  classical
  have : ∀ k, IsProbabilityMeasure (P.map (M k).Zd) := fun k =>
    (Measure.isProbabilityMeasure_map_iff (M k).measurable_Zd.aemeasurable).2 ‹_›
  have hCMall := ae_all_iff.2 fun k => (M k).cm_shift (hh k) hδ0 hδ10
  filter_upwards [hCMall] with x hx
  choose T ρ hρm hρ0 V hV0 hVM hmom hcm hshift using hx
  have hρm' : Measurable fun z : ι → DistOn (ballO 0 1) => ∏ k, ρ k (z k) :=
    Finset.measurable_prod _ fun k _ => (hρm k).comp (measurable_pi_apply k)
  refine ⟨fun z => ∏ k, ρ k (z k), hρm', fun z => Finset.prod_nonneg fun k _ => (hρ0 k _).le,
    ∑ k, V k, Finset.sum_nonneg fun k _ => hV0 k, Finset.sum_le_sum fun k _ => hVM k, ?_, ?_⟩
  · intro s
    rw [hZmap, lintegral_pi_prod_rpow hρm hρ0 s]
    simp_rw [hmom]
    rw [← ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum, Finset.sum_div]
  · intro c
    rw [hZmap]
    have hadd : ∀ k, Measurable fun z : DistOn (ballO 0 1) => z + T k := fun k =>
      measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const (T k φ)
    have hΨ : Measurable fun z : ι → DistOn (ballO 0 1) =>
        ENNReal.ofReal (PhiN δ Fn (EdN M x.2, c, z)) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_PhiN δ hFn).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    have H := lintegral_pi_shift (ν := fun k => P.map (M k).Zd) hadd hρm hcm hΨ
    calc ∫⁻ z, ENNReal.ofReal (PhiN δ Fn (EdN M x.1, c, z)) ∂Measure.pi (fun k => P.map (M k).Zd)
        = ∫⁻ z, ENNReal.ofReal (PhiN δ Fn (EdN M x.2, c, z + T))
            ∂Measure.pi (fun k => P.map (M k).Zd) := by
          refine lintegral_congr fun z => ?_
          simp only [PhiN, EdN]
          congr 3
          funext k
          exact hshift k (z k) (c k)
      _ = _ := H
      _ = ∫⁻ z, ENNReal.ofReal (PhiN δ Fn (EdN M x.2, c, z)) * ENNReal.ofReal (∏ k, ρ k (z k))
            ∂Measure.pi (fun k => P.map (M k).Zd) := by
          refine lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_prod_of_nonneg fun k _ => (hρ0 k _).le]

/-- **The exponential moment of `∑_k MfG_k`** by Hölder's inequality from the one-field bound at `N κ`. -/
theorem lintegral_exp_MfN_le (hh : ∀ k, IsWholePlaneGFF (h k) P) (M : ∀ k, DiskMarkov P (h k))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ10 : δ < 1 / 10) (hN : 0 < Fintype.card ι) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : 200 * (25 * Real.pi * ((Fintype.card ι : ℝ) * κ) * energyConst) * logCovConst * δ ^ 2 ≤
      massQ ^ 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (κ * MfN M δ x)) ∂(P.prod P) ≤ ENNReal.ofReal 2 := by
  set N := Fintype.card ι with hNdef
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hNκ0 : 0 ≤ (N : ℝ) * κ := by positivity
  have hmomk : ∀ k, ∫⁻ x, ENNReal.ofReal (Real.exp (((N : ℝ) * κ) * (M k).MfG δ x))
      ∂(P.prod P) ≤ ENNReal.ofReal 2 := fun k =>
    (M k).lintegral_exp_MfG_le (hh k) hδ0 hδ10 hNκ0 hκ
  set f : ι → Ω × Ω → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal (Real.exp (((N : ℝ) * κ) * (M k).MfG δ x)) with hfdef
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (Real.measurable_exp.comp (((M k).measurable_MfG (hh k).measurable δ).const_mul _)).ennreal_ofReal
  have e : ∀ x, ENNReal.ofReal (Real.exp (κ * MfN M δ x)) = ∏ k, f k x ^ (1 / (N : ℝ)) := by
    intro x
    rw [MfN, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hfdef, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
    congr 2
    field_simp
  have hsum : ∑ k ∈ (Finset.univ : Finset ι), (1 / (N : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ← hNdef, nsmul_eq_mul]
    field_simp
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (κ * MfN M δ x)) ∂(P.prod P)
      = ∫⁻ x, ∏ k, f k x ^ (1 / (N : ℝ)) ∂(P.prod P) := lintegral_congr e
    _ ≤ ∏ k, (∫⁻ x, f k x ∂(P.prod P)) ^ (1 / (N : ℝ)) :=
        ENNReal.lintegral_prod_norm_pow_le Finset.univ (fun k _ => (hfm k).aemeasurable) hsum
          (fun k _ => by positivity)
    _ ≤ ∏ _k : ι, ENNReal.ofReal 2 ^ (1 / (N : ℝ)) :=
        Finset.prod_le_prod fun k _ => ENNReal.rpow_le_rpow (hmomk k) (by positivity)
    _ = ENNReal.ofReal 2 := by
        rw [Finset.prod_const, Finset.card_univ, ← hNdef, ← ENNReal.rpow_mul_natCast,
          one_div_mul_cancel hNr.ne', ENNReal.rpow_one]

omit [Fintype ι] in
/-- the parameter inequality for `lintegral_exp_MfN_le` at `q = A_N/δ`, `κ = 2 s θ q²` -/
lemma a3AN_energy {N : ℕ} (hN : 0 < N) (hp : 1 ≤ p) (hpp₀ : p < p₀) {δ : ℝ} (hδ0 : 0 < δ) :
    200 * (25 * Real.pi * ((N : ℝ) * (2 * cplExp p p₀ * (1 - 1 / p₀) * (a3AN p p₀ N / δ) ^ 2)) *
      energyConst) * logCovConst * δ ^ 2 ≤ massQ ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp₀1 : 1 < p₀ := by linarith
  have hp₀ : 0 < p₀ := by linarith
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set sc := cplExp p p₀ with hsc
  set θ := 1 - 1 / p₀ with hθ
  have hsc0 : 0 ≤ sc := by
    rw [hsc, cplExp]; exact mul_nonneg hp0.le (div_nonneg hp₀.le (by linarith))
  have hθ0 : 0 ≤ θ := by rw [hθ, sub_nonneg, div_le_one hp₀]; exact hp₀1.le
  have hE0 := energyConst_nonneg
  have hL0 := logCovConst_nonneg
  set A₁ := a3A p p₀ with hA₁
  have hA2 : A₁ ^ 2 = massQ ^ 2 / (200 * (25 * Real.pi * (|2 * sc * θ| + 1) *
      (energyConst + 1)) * (logCovConst + 1)) := by
    rw [hA₁, a3A, Real.sq_sqrt (by positivity)]
  have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNr.le
  have hsq0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hκδ : (N : ℝ) * (2 * sc * θ * (a3AN p p₀ N / δ) ^ 2) * δ ^ 2 = 2 * sc * θ * A₁ ^ 2 := by
    rw [a3AN, ← hA₁]
    field_simp
    rw [hsq]
    ring
  have hden : 0 < 200 * (25 * Real.pi * (|2 * sc * θ| + 1) * (energyConst + 1)) *
      (logCovConst + 1) := by positivity
  calc 200 * (25 * Real.pi * ((N : ℝ) * (2 * sc * θ * (a3AN p p₀ N / δ) ^ 2)) * energyConst) *
        logCovConst * δ ^ 2
      = 200 * 25 * Real.pi * energyConst * logCovConst *
          ((N : ℝ) * (2 * sc * θ * (a3AN p p₀ N / δ) ^ 2) * δ ^ 2) := by ring
    _ = 200 * 25 * Real.pi * (2 * sc * θ) * energyConst * logCovConst * A₁ ^ 2 := by
        rw [hκδ]; ring
    _ ≤ 200 * 25 * Real.pi * (|2 * sc * θ| + 1) * (energyConst + 1) * (logCovConst + 1) *
        A₁ ^ 2 := by
        have h1 : 2 * sc * θ ≤ |2 * sc * θ| + 1 := (le_abs_self _).trans (by linarith)
        gcongr
        · linarith
        · linarith
    _ = massQ ^ 2 := by rw [hA2]; field_simp

/-- **[18] Lemma A.3 for `N` fields and a nonnegative functional**, with the tail constant of
`lemmaA3_product`. -/
theorem lemmaA3N_nonneg (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs0 : 0 < s)
    (hh : ∀ k, IsWholePlaneGFF (h k) P) (hind : iIndepFun h P) (hball : ball (0 : ℂ) 1 ⊆ ball w R)
    (hn : ∀ k, ∀ᵐ ω ∂P, circleAvg (h k ω) R w = 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδa : δ ≤ a3aN p p₀ (Fintype.card ι))
    {Fn : (ι → DistOn (ballO 0 δ)) × (ι → ℝ) → ℝ} (hFn : Measurable Fn) (hFn0 : ∀ x, 0 ≤ Fn x)
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal (Fn (obsN δ h ω)) ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal |P[fun ω => Fn (obsN δ h ω) | extSigmaN h] ω -
        P[fun ω => Fn (obsN δ h ω) | cSigmaN h] ω| ^ p ∂P ≤
      2 ^ (p - 1) * (ENNReal.ofReal (δ ^ s) ^ p * ∫⁻ ω, ENNReal.ofReal (Fn (obsN δ h ω)) ^ p ∂P +
        (∫⁻ ω, ENNReal.ofReal (Fn (obsN δ h ω)) ^ p₀ ∂P) ^ (p / p₀) *
          ENNReal.ofReal (cplTail p p₀ (a3AN p p₀ (Fintype.card ι) / δ) (δ ^ s) 2) ^ (1 - p / p₀)) := by
  have hp0 : 0 < p := by linarith
  have hp₀1 : 1 < p₀ := by linarith
  have hp₀ : 0 < p₀ := by linarith
  have hN : 0 < Fintype.card ι := by
    by_contra hN0
    have hN0' : Fintype.card ι = 0 := by omega
    have hA : a3AN p p₀ (Fintype.card ι) = 0 := by simp [a3AN, hN0']
    have : a3aN p p₀ (Fintype.card ι) ≤ 0 := by
      unfold a3aN; rw [hA, zero_div]; exact min_le_right _ _
    linarith
  have hNr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hN
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
  choose M hMz using fun k => exists_diskMarkov_meas (hh k) hR (hn k) hdisj
  have h𝓖 : extSigmaN h ≤ ‹MeasurableSpace Ω› := iSup_le fun k => extSigma_le (hh k).measurable
  -- parameters
  have hA0 : 0 < a3AN p p₀ (Fintype.card ι) := div_pos (a3A_pos p p₀) (Real.sqrt_pos.2 hNr)
  have hδ20 : δ ≤ 1 / 20 := hδa.trans (min_le_left _ _)
  have hδ10 : δ < 1 / 10 := by linarith
  have hδA : δ ≤ a3AN p p₀ (Fintype.card ι) / max 1 (p₀ / (p₀ - 1)) :=
    hδa.trans (min_le_right _ _)
  have hmax : 0 < max 1 (p₀ / (p₀ - 1)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hqmax : max 1 (p₀ / (p₀ - 1)) ≤ a3AN p p₀ (Fintype.card ι) / δ := by
    rw [le_div_iff₀ hδ0]
    rw [le_div_iff₀ hmax] at hδA
    linarith
  have hq1 : 1 ≤ a3AN p p₀ (Fintype.card ι) / δ := (le_max_left _ _).trans hqmax
  have hqr : p₀ / (p₀ - 1) ≤ a3AN p p₀ (Fintype.card ι) / δ := (le_max_right _ _).trans hqmax
  have ht0 : 0 ≤ δ ^ s := (Real.rpow_pos_of_pos hδ0 s).le
  have ht1 : δ ^ s < 1 := Real.rpow_lt_one hδ0.le (by linarith) hs0
  have hsc0 : 0 ≤ cplExp p p₀ := by
    rw [cplExp]; exact mul_nonneg hp0.le (div_nonneg hp₀.le (by linarith))
  have hθ0 : 0 ≤ 1 - 1 / p₀ := by rw [sub_nonneg, div_le_one hp₀]; exact hp₀1.le
  have hκ0 : 0 ≤ 2 * cplExp p p₀ * (1 - 1 / p₀) * (a3AN p p₀ (Fintype.card ι) / δ) ^ 2 := by
    positivity
  -- the data and the three ingredients
  obtain ⟨hind', hCEZ, hEZ, hZmap⟩ := indep_dataN hh hind M hMz hR hnest hn
  have hE𝓖 : Measurable[extSigmaN h] (EdN M) := measurable_pi_of fun k =>
    (M k).measurable_Ed_ext.mono (le_iSup (fun k => extSigma (h k)) k) le_rfl
  have hC𝓖 : Measurable[extSigmaN h] (cAvgN h) := measurable_pi_of fun k =>
    (DiskMarkov.measurable_cAvg_ext (h k)).mono (le_iSup (fun k => extSigma (h k)) k) le_rfl
  have hZ : Measurable (ZdN M) := measurable_pi_iff.2 fun k => (M k).measurable_Zd
  have hBsub : ballO (0 : ℂ) δ ≤ ballO 0 1 := fun z hz => by
    show z ∈ ball (0 : ℂ) 1
    have : z ∈ ball (0 : ℂ) δ := hz
    rw [mem_ball, dist_zero_right] at this ⊢; linarith
  have hXΦ : (fun ω => Fn (obsN δ h ω)) =ᵐ[P] fun ω => PhiN δ Fn (EdN M ω, cAvgN h ω, ZdN M ω) := by
    filter_upwards [ae_all_iff.2 fun k => (M k).restrictTo_eq] with ω h2
    simp only [PhiN, obsN]
    refine congrArg Fn (Prod.ext ?_ rfl)
    funext k
    show restrictTo (ballO 0 δ) (h k ω) = _
    rw [← resOn_restrictTo hBsub, h2 k]
    rfl
  have hCM := cm_pointwiseN hh M hZmap hδ0 hδ10 hFn
  have hmom := lintegral_exp_MfN_le hh M hδ0 hδ10 hN hκ0 (a3AN_energy hN hp hpp₀ hδ0)
  exact lemmaA3_product (P := P) (𝓖 := extSigmaN h) h𝓖 hE𝓖 hC𝓖 hZ hind' hCEZ hEZ
    (measurable_PhiN δ hFn) (fun x => hFn0 _) hXΦ hp hpp₀ hq1 hqr ht0 ht1
    (Finset.measurable_sum _ fun k _ => (M k).measurable_MfG (hh k).measurable δ) hCM hmom hXp₀

/-- **[18] Lemma A.3** (`N`-tuple of independent whole-plane GFFs, `p ≥ 1`): for `h = (h^k)_{k ∈ ι}` independent
whole-plane GFFs each normalized so that `h^k_R(w) = 0` with `𝔻 ⊆ B_R(w)`, `N = |ι|`, `δ ∈ (0, a]` and
`X = F((h^k|_{B_δ(0)})_k, (h^k_1(0))_k)`,
`E|E[X | σ(h|_{ℂ∖𝔻})] − E[X | σ(h_1(0))]|^p ≤ C (δ^{sp} E|X|^p + e^{−b/δ^{1−s}} E[|X|^{p₀}]^{p/p₀})`
with `a = a3aN p p₀ N`, `b = a3bN p p₀ N`, `C = a3C p p₀` (independent of `w`, `R`, `δ`, `X`). -/
theorem lemmaA3N (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs0 : 0 < s)
    (hh : ∀ k, IsWholePlaneGFF (h k) P) (hind : iIndepFun h P) (hball : ball (0 : ℂ) 1 ⊆ ball w R)
    (hn : ∀ k, ∀ᵐ ω ∂P, circleAvg (h k ω) R w = 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδa : δ ≤ a3aN p p₀ (Fintype.card ι))
    {X : Ω → ℝ} {F : (ι → DistOn (ballO 0 δ)) × (ι → ℝ) → ℝ} (hF : Measurable F)
    (hX : X =ᵐ[P] fun ω =>
      F (fun k => restrictTo (ballO 0 δ) (h k ω), fun k => circleAvg (h k ω) 1 0))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal |P[X | extSigmaN h] ω - P[X | cSigmaN h] ω| ^ p ∂P ≤
      ENNReal.ofReal (a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) * ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P +
          ENNReal.ofReal (Real.exp (-(a3bN p p₀ (Fintype.card ι) / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P) ^ (p / p₀)) := by
  have hp0 : 0 < p := by linarith
  have hp₀ : 0 < p₀ := by linarith
  have hhm : ∀ k, Measurable (h k) := fun k => (hh k).measurable
  have hGle : extSigmaN h ≤ ‹MeasurableSpace Ω› := iSup_le fun k => extSigma_le (hh k).measurable
  have hHle : cSigmaN h ≤ ‹MeasurableSpace Ω› :=
    (measurable_pi_of fun k => (measurable_circleAvg_left 1 0).comp (hhm k)).comap_le
  have H := condExp_sub_rpow_of_nonneg hGle hHle (measurable_obsN δ hhm) hp hpp₀
    (ENNReal.ofReal (δ ^ s) ^ p)
    (ENNReal.ofReal (cplTail p p₀ (a3AN p p₀ (Fintype.card ι) / δ) (δ ^ s) 2) ^ (1 - p / p₀))
    (fun Fn hFn hFn0 hfin => lemmaA3N_nonneg hp hpp₀ hs0 hh hind hball hn hδ0 hδa hFn hFn0 hfin)
    hF hX hXp₀
  set Ip := ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P
  set Ip₀ := ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P
  have hT : ENNReal.ofReal (cplTail p p₀ (a3AN p p₀ (Fintype.card ι) / δ) (δ ^ s) 2) ^
      (1 - p / p₀) = ENNReal.ofReal (((2 : ℝ) ^ cplExp p p₀ * 2) ^ (1 - p / p₀)) *
      ENNReal.ofReal (Real.exp (-(a3bN p p₀ (Fintype.card ι) / δ ^ (1 - s)))) := by
    rw [cplTail_rpow_eq_of hp hpp₀ _ s hδ0, a3bN]
  set C₁ : ℝ := ((2 : ℝ) ^ cplExp p p₀ * 2) ^ (1 - p / p₀)
  have hC₁ : 0 ≤ C₁ := by positivity
  have hδsp : ENNReal.ofReal (δ ^ s) ^ p = ENNReal.ofReal (δ ^ (s * p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_pos_of_pos hδ0 s).le hp0.le, ← Real.rpow_mul hδ0.le]
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]; norm_num
  set eb := ENNReal.ofReal (Real.exp (-(a3bN p p₀ (Fintype.card ι) / δ ^ (1 - s))))
  calc ∫⁻ ω, ENNReal.ofReal |P[X | extSigmaN h] ω - P[X | cSigmaN h] ω| ^ p ∂P
      ≤ 2 ^ (p - 1) * 2 ^ (p - 1) * 2 * (ENNReal.ofReal (δ ^ s) ^ p * Ip + Ip₀ ^ (p / p₀) *
          ENNReal.ofReal (cplTail p p₀ (a3AN p p₀ (Fintype.card ι) / δ) (δ ^ s) 2) ^
            (1 - p / p₀)) := H
    _ = ENNReal.ofReal (2 ^ (p - 1) * 2 ^ (p - 1) * 2) *
          (ENNReal.ofReal (δ ^ (s * p)) * Ip + ENNReal.ofReal C₁ * (eb * Ip₀ ^ (p / p₀))) := by
        rw [hT, hδsp, h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (2 ^ (p - 1) * 2 ^ (p - 1) * 2) *
          (ENNReal.ofReal (max 1 C₁) * (ENNReal.ofReal (δ ^ (s * p)) * Ip) +
            ENNReal.ofReal (max 1 C₁) * (eb * Ip₀ ^ (p / p₀))) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · calc ENNReal.ofReal (δ ^ (s * p)) * Ip = 1 * (ENNReal.ofReal (δ ^ (s * p)) * Ip) :=
                (one_mul _).symm
            _ ≤ ENNReal.ofReal (max 1 C₁) * (ENNReal.ofReal (δ ^ (s * p)) * Ip) := by
                refine mul_le_mul' ?_ le_rfl
                rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
        · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
    _ = ENNReal.ofReal (a3C p p₀) * (ENNReal.ofReal (δ ^ (s * p)) * Ip + eb * Ip₀ ^ (p / p₀)) := by
        rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), a3C]

end

end MatedCRTHarmonic.GMSAppA
