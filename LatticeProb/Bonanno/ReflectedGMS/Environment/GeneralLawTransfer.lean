/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GeneralLawTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLaws
import LatticeProb.Bonanno.ReflectedGMS.Environment.CodeGeneralValid
import LatticeProb.Bonanno.ReflectedGMS.HarmonicLawIngredients
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Util.AssertNoSorry

/-!
# Transfer of the random-environment hypotheses from general to finite-row environments

Theorems 1.2 and 1.3 of the general-cell manuscript are stated for a raw law `P` carried by
general environments (`GeneralLaws.SupportedOnValidGeneral`, Definition 1.1 + (LCS), no graph local
finiteness), while the proved main theorems of the earlier development take the lifted law
`EnvironmentLaws.validLaw` on `Code.Env` (finite rows).  This file transfers the three
random-environment hypotheses, **mass transport modulo scaling**, the **(FE) moment** and
**ergodicity modulo scaling**, from `generalLaw P hP` to `validLaw P hV`.

The general results take two inputs as explicit hypotheses:

* `hA : ∀ r, ValidGeneral r → FiniteRows r → Valid r` — the pathwise adapter, proved as
  `Code.valid_of_validGeneral`; the `…_of_generalLaw` corollaries at the end discharge it;
* `hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val` — Lemma 2.5 (a.s. graph local finiteness),
  proved in another packet, and the only remaining input of the corollaries.

Main results.

* `supportedOnValid_of_ae_finiteRows` — `P` is carried by `Code.Valid`.
* `lintegral_validLaw_eq` — every nonnegative measurable observable of `Env` has the same
  `validLaw` integral as its zero extension to `EnvGeneral` under `generalLaw` (Doob–Dynkin through
  the trace σ-algebra, with no measurability of `Valid` or `ValidGeneral`).
* `massTransport_validLaw` — an old kernel is extended by zero off the (measurable) finite-row
  set; general similarities preserve finite rows and between finite-row environments **are** old
  similarities, so the extension is a general kernel.
* `finiteEnergyMoment_validLaw` — pointwise the old (real-sum) density is bounded by the new
  (extended-sum) density; indeed they agree at finite-row environments.
* `environmentErgodic_validLaw` — an invariant event `val⁻¹' B` of `Env` corresponds to the
  invariant event `{FiniteRows} ∩ val⁻¹' B` of `EnvGeneral`, with the same probability.

Searched before writing: mathlib `Measurable.exists_eq_measurable_comp` (Doob–Dynkin, reused),
`ENNReal.ofReal_tsum_of_nonneg` (reused; mathlib has no unconditional `ofReal (∑') ≤ ∑' ofReal`),
project `rootAt` congruence lemmas (none; one added), and
`RootedFiniteEnergyDensityMeasurable.measurable_rootedFiniteEnergyDensity_zero` (reused).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS

namespace GeneralLaws

open Code

/-! ### Finite rows form a measurable set of codes -/

/-- `FiniteRows` is a Borel condition on raw codes: every row vanishes beyond some index. -/
theorem measurableSet_finiteRows : MeasurableSet {r : RawCode | FiniteRows r} := by
  have hset : {r : RawCode | FiniteRows r} =
      ⋂ n : ℕ, ⋃ N : ℕ, ⋂ m : ℕ, {r : RawCode | r.2 n m = 0 ∨ m ≤ N} := by
    ext r
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion]
    refine forall_congr' fun n => ?_
    constructor
    · intro h
      obtain ⟨N, hN⟩ := h.bddAbove
      refine ⟨N, fun m => ?_⟩
      by_cases hm : r.2 n m = 0
      · exact Or.inl hm
      · exact Or.inr (hN hm)
    · rintro ⟨N, hN⟩
      refine (Set.finite_Iic N).subset fun m hm => ?_
      rcases hN m with h | h
      · exact absurd h hm
      · exact h
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun m => ?_
  have hm : Measurable fun r : RawCode => r.2 n m :=
    (measurable_pi_apply m).comp ((measurable_pi_apply n).comp measurable_snd)
  exact (hm (measurableSet_singleton 0)).union (MeasurableSet.const (m ≤ N))

/-- The finite-row environments form a measurable set of general environments. -/
theorem measurableSet_finiteRows_envGeneral :
    MeasurableSet {e : EnvGeneral | FiniteRows e.val} :=
  measurable_subtype_coe measurableSet_finiteRows

/-! ### Similarities preserve finite rows -/

/-- A conductance-preserving relabelling of active vertices carries finite rows to finite rows
(inactive labels have zero rows by admissibility). -/
theorem finiteRows_of_relabel {r r' : RawCode} (h' : RawAdmissible r')
    (σ : Vertex r ≃ Vertex r')
    (hc : ∀ v w, r'.2 (σ v).val (σ w).val = r.2 v.val w.val) (hr : FiniteRows r) :
    FiniteRows r' := by
  intro n
  by_cases hn : (r'.1 n).isSome
  · have key : ∀ w : Vertex r, r'.2 n (σ w).val = r.2 (σ.symm ⟨n, hn⟩).val w.val := by
      intro w
      have h1 := hc (σ.symm ⟨n, hn⟩) w
      rw [Equiv.apply_symm_apply] at h1
      exact h1
    have hfin : (Subtype.val ⁻¹' Function.support (r.2 (σ.symm ⟨n, hn⟩).val) :
        Set (Vertex r)).Finite :=
      (hr (σ.symm ⟨n, hn⟩).val).preimage Subtype.val_injective.injOn
    refine (hfin.image fun w => (σ w).val).subset ?_
    intro m hm
    have hm' : (r'.1 m).isSome := by
      by_contra hms
      apply hm
      exact h'.absent n m (Or.inr (Option.not_isSome_iff_eq_none.mp hms))
    refine ⟨σ.symm ⟨m, hm'⟩, ?_, by simp⟩
    have h2 := key (σ.symm ⟨m, hm'⟩)
    rw [Equiv.apply_symm_apply] at h2
    show r.2 (σ.symm ⟨n, hn⟩).val (σ.symm ⟨m, hm'⟩).val ≠ 0
    rw [← h2]
    exact hm
  · have hzero : Function.support (r'.2 n) = ∅ := by
      ext m
      simp only [Function.mem_support, ne_eq, mem_empty_iff_false, iff_false, not_not]
      exact h'.absent n m (Or.inl (Option.not_isSome_iff_eq_none.mp hn))
    rw [hzero]
    exact finite_empty

/-- General similarities preserve finite rows, in both directions. -/
theorem finiteRows_iff_of_isSimilarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : EnvGeneral}
    (hsim : IsSimilarity s u hs e e') : FiniteRows e.val ↔ FiniteRows e'.val := by
  obtain ⟨σ, -, hc⟩ := hsim
  constructor
  · exact finiteRows_of_relabel e'.property.choose σ hc
  · refine finiteRows_of_relabel e.property.choose σ.symm ?_
    intro v w
    have h1 := hc (σ.symm v) (σ.symm w)
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm

/-! ### Finite-row general environments as environments of the earlier development -/

section Adapter

variable (hA : ∀ r, ValidGeneral r → FiniteRows r → Valid r)

/-- A finite-row general environment, viewed in `Code.Env` through the adapter `hA`. -/
def envOfFiniteRows (e : EnvGeneral) (h : FiniteRows e.val) : Env :=
  ⟨e.val, hA e.val e.property h⟩

/-- Between finite-row environments a general similarity is a similarity of the earlier
development, with the same relabelling: both read the same cells and conductances. -/
theorem isSimilarity_envOfFiniteRows {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : EnvGeneral}
    (hsim : IsSimilarity s u hs e e') (he : FiniteRows e.val) (he' : FiniteRows e'.val) :
    EnvironmentLaws.IsSimilarity s u hs (envOfFiniteRows hA e he) (envOfFiniteRows hA e' he') := by
  obtain ⟨σ, hcell, hc⟩ := hsim
  exact ⟨σ, hcell, hc⟩

open Classical in
/-- The measurable totalisation of `envOfFiniteRows`, sending infinite-row environments to a fixed
environment `d`. -/
noncomputable def envOfFiniteRowsOr (d : Env) (e : EnvGeneral) : Env :=
  if h : FiniteRows e.val then envOfFiniteRows hA e h else d

theorem envOfFiniteRowsOr_of_finiteRows (d : Env) (e : EnvGeneral) (h : FiniteRows e.val) :
    envOfFiniteRowsOr hA d e = envOfFiniteRows hA e h := by
  classical
  exact dif_pos h

theorem measurable_envOfFiniteRowsOr (d : Env) : Measurable (envOfFiniteRowsOr hA d) := by
  classical
  have hval : (fun e : EnvGeneral => (envOfFiniteRowsOr hA d e).val) =
      fun e => if FiniteRows e.val then e.val else d.val := by
    funext e
    by_cases h : FiniteRows e.val
    · rw [envOfFiniteRowsOr_of_finiteRows hA d e h, if_pos h]
      rfl
    · rw [if_neg h]
      show (dite (FiniteRows e.val) (fun h => envOfFiniteRows hA e h) fun _ => d).val = d.val
      rw [dif_neg h]
  have hm : Measurable fun e : EnvGeneral => (envOfFiniteRowsOr hA d e).val := by
    rw [hval]
    exact Measurable.ite measurableSet_finiteRows_envGeneral measurable_subtype_coe
      measurable_const
  exact hm.subtype_mk

end Adapter

/-! ### The zero extension of integrals -/

section Laws

variable (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValidGeneral P)
  (hA : ∀ r, ValidGeneral r → FiniteRows r → Valid r)

/-- Lemma 2.5 transported to the raw law: `P`-almost every code has finite rows. -/
theorem ae_finiteRows_raw (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val) :
    ∀ᵐ r ∂P, FiniteRows r := by
  rw [← map_generalLaw P hP]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_finiteRows).2 hfin

include hA in
/-- **The raw law is carried by valid (finite-row) environments.** -/
theorem supportedOnValid_of_ae_finiteRows
    (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val) : EnvironmentLaws.SupportedOnValid P := by
  have hP' : ∀ᵐ r ∂P, ValidGeneral r := hP
  show ∀ᵐ r ∂P, Valid r
  filter_upwards [hP', ae_finiteRows_raw P hP hfin] with r h1 h2 using hA r h1 h2

open Classical in
/-- **Integrals under `validLaw` are integrals under `generalLaw` of the zero extension.** -/
theorem lintegral_validLaw_eq (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val)
    (hV : EnvironmentLaws.SupportedOnValid P) {g : Env → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ e, g e ∂EnvironmentLaws.validLaw P hV =
      ∫⁻ e, (if h : FiniteRows e.val then g (envOfFiniteRows hA e h) else 0) ∂generalLaw P hP := by
  obtain ⟨G, hG, hgG⟩ :=
    Measurable.exists_eq_measurable_comp (f := (Subtype.val : Env → RawCode)) hg
  have hgG' : ∀ e, g e = G e.val := fun e => congrFun hgG e
  calc ∫⁻ e, g e ∂EnvironmentLaws.validLaw P hV
        = ∫⁻ e, G e.val ∂EnvironmentLaws.validLaw P hV := lintegral_congr fun e => hgG' e
    _ = ∫⁻ r, G r ∂((EnvironmentLaws.validLaw P hV).map Subtype.val) :=
        (lintegral_map hG measurable_subtype_coe).symm
    _ = ∫⁻ r, G r ∂P := by rw [EnvironmentLaws.map_validLaw]
    _ = ∫⁻ r, G r ∂((generalLaw P hP).map Subtype.val) := by rw [map_generalLaw]
    _ = ∫⁻ e, G e.val ∂generalLaw P hP := lintegral_map hG measurable_subtype_coe
    _ = ∫⁻ e, (if h : FiniteRows e.val then g (envOfFiniteRows hA e h) else 0)
          ∂generalLaw P hP := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with e he
        rw [dif_pos he, hgG']
        rfl

/-! ### Mass transport -/

section Kernel

variable (T : EnvironmentLaws.MassTransportKernel) (d : Env)

open Classical in
/-- The zero extension of an old transport kernel to general environments. -/
noncomputable def extendedKernelFun (x : EnvGeneral × Plane × Plane) : ℝ≥0∞ :=
  if FiniteRows x.1.val then T.toFun (envOfFiniteRowsOr hA d x.1, x.2) else 0

theorem extendedKernelFun_of_finiteRows (e : EnvGeneral) (h : FiniteRows e.val) (w z : Plane) :
    extendedKernelFun hA T d (e, w, z) = T.toFun (envOfFiniteRows hA e h, w, z) := by
  classical
  show (if FiniteRows e.val then T.toFun (envOfFiniteRowsOr hA d e, w, z) else 0) = _
  rw [if_pos h, envOfFiniteRowsOr_of_finiteRows hA d e h]

theorem extendedKernelFun_of_not_finiteRows (e : EnvGeneral) (h : ¬ FiniteRows e.val)
    (w z : Plane) : extendedKernelFun hA T d (e, w, z) = 0 := by
  classical
  show (if FiniteRows e.val then T.toFun (envOfFiniteRowsOr hA d e, w, z) else 0) = _
  rw [if_neg h]

theorem measurable_extendedKernelFun : Measurable (extendedKernelFun hA T d) := by
  classical
  show Measurable fun x : EnvGeneral × Plane × Plane =>
    if FiniteRows x.1.val then T.toFun (envOfFiniteRowsOr hA d x.1, x.2) else 0
  refine Measurable.ite (measurable_fst measurableSet_finiteRows_envGeneral) ?_ measurable_const
  exact T.measurable_toFun.comp
    (((measurable_envOfFiniteRowsOr hA d).comp measurable_fst).prodMk measurable_snd)

/-- The zero extension is a transport kernel of degree `−2` on general environments. -/
noncomputable def extendedKernel : MassTransportKernel where
  toFun := extendedKernelFun hA T d
  measurable_toFun := measurable_extendedKernelFun hA T d
  covariant s u hs e e' hsim w z := by
    by_cases he : FiniteRows e.val
    · have he' : FiniteRows e'.val := (finiteRows_iff_of_isSimilarity hsim).1 he
      rw [extendedKernelFun_of_finiteRows hA T d e' he', extendedKernelFun_of_finiteRows hA T d e he]
      exact T.covariant s u hs _ _ (isSimilarity_envOfFiniteRows hA hsim he he') w z
    · have he' : ¬ FiniteRows e'.val := fun h => he ((finiteRows_iff_of_isSimilarity hsim).2 h)
      rw [extendedKernelFun_of_not_finiteRows hA T d e' he',
        extendedKernelFun_of_not_finiteRows hA T d e he, mul_zero]

end Kernel

include hA in
/-- **Mass transport transfers** from the general law to the lifted valid law. -/
theorem massTransport_validLaw (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val)
    (hV : EnvironmentLaws.SupportedOnValid P) (hMT : MassTransport (generalLaw P hP)) :
    EnvironmentLaws.MassTransport (EnvironmentLaws.validLaw P hV) := by
  classical
  intro T
  have hV' : ∀ᵐ r ∂P, Valid r := hV
  obtain ⟨r, hr⟩ := hV'.exists
  let d : Env := ⟨r, hr⟩
  have hout : Measurable fun e : Env => ∫⁻ z : Plane, T.toFun (e, 0, z) ∂volume :=
    T.measurable_outgoing.lintegral_prod_right'
  have hin : Measurable fun e : Env => ∫⁻ z : Plane, T.toFun (e, z, 0) ∂volume :=
    T.measurable_incoming.lintegral_prod_right'
  rw [lintegral_validLaw_eq P hP hA hfin hV hout, lintegral_validLaw_eq P hP hA hfin hV hin]
  have hL : ∀ e : EnvGeneral,
      (∫⁻ z : Plane, (extendedKernel hA T d).toFun (e, 0, z) ∂volume) =
        if h : FiniteRows e.val then ∫⁻ z : Plane, T.toFun (envOfFiniteRows hA e h, 0, z) ∂volume
        else 0 := by
    intro e
    by_cases he : FiniteRows e.val
    · rw [dif_pos he]
      exact lintegral_congr fun z => extendedKernelFun_of_finiteRows hA T d e he 0 z
    · rw [dif_neg he]
      calc (∫⁻ z : Plane, (extendedKernel hA T d).toFun (e, 0, z) ∂volume)
          = ∫⁻ _z : Plane, (0 : ℝ≥0∞) ∂volume :=
            lintegral_congr fun z => extendedKernelFun_of_not_finiteRows hA T d e he 0 z
        _ = 0 := lintegral_zero
  have hR : ∀ e : EnvGeneral,
      (∫⁻ z : Plane, (extendedKernel hA T d).toFun (e, z, 0) ∂volume) =
        if h : FiniteRows e.val then ∫⁻ z : Plane, T.toFun (envOfFiniteRows hA e h, z, 0) ∂volume
        else 0 := by
    intro e
    by_cases he : FiniteRows e.val
    · rw [dif_pos he]
      exact lintegral_congr fun z => extendedKernelFun_of_finiteRows hA T d e he z 0
    · rw [dif_neg he]
      calc (∫⁻ z : Plane, (extendedKernel hA T d).toFun (e, z, 0) ∂volume)
          = ∫⁻ _z : Plane, (0 : ℝ≥0∞) ∂volume :=
            lintegral_congr fun z => extendedKernelFun_of_not_finiteRows hA T d e he z 0
        _ = 0 := lintegral_zero
  have h := hMT (extendedKernel hA T d)
  calc (∫⁻ e, (if h : FiniteRows e.val then
          ∫⁻ z : Plane, T.toFun (envOfFiniteRows hA e h, 0, z) ∂volume else 0) ∂generalLaw P hP)
      = ∫⁻ e, ∫⁻ z : Plane, (extendedKernel hA T d).toFun (e, 0, z) ∂volume ∂generalLaw P hP :=
        lintegral_congr fun e => (hL e).symm
    _ = ∫⁻ e, ∫⁻ z : Plane, (extendedKernel hA T d).toFun (e, z, 0) ∂volume ∂generalLaw P hP := h
    _ = ∫⁻ e, (if h : FiniteRows e.val then
          ∫⁻ z : Plane, T.toFun (envOfFiniteRows hA e h, z, 0) ∂volume else 0) ∂generalLaw P hP :=
        lintegral_congr fun e => hR e

/-! ### The (FE) moment -/

/-- For nonnegative terms, the real sum embeds below the extended sum (with equality when
summable, and `0` on the left otherwise). -/
theorem ofReal_tsum_le_tsum_ofReal {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∑' a, f a) ≤ ∑' a, ENNReal.ofReal (f a) := by
  by_cases hs : Summable f
  · exact (ENNReal.ofReal_tsum_of_nonneg hf hs).le
  · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
    exact zero_le ..

/-- `rootAt` reads only the cells. -/
theorem rootAt_eq_of_cell_eq {V : Type*} {F F' : IndexedCells V} (h : F.cell = F'.cell)
    (z : Plane) : RootDensities.rootAt F z = RootDensities.rootAt F' z := by
  obtain ⟨c, g⟩ := F
  obtain ⟨c', g'⟩ := F'
  simp only at h
  subst h
  rfl

/-- At a vertex of a valid environment, the earlier (FE) integrand, with real conductance sums,
is bounded by the general one, with extended sums. -/
theorem finiteEnergyDensity_decode_le (e : EnvGeneral) (hv : Valid e.val) (v : Vertex e.val) :
    RootDensities.finiteEnergyDensity (decode ⟨e.val, hv⟩) v ≤
      finiteEnergyDensity (config e) v := by
  have hpi : ENNReal.ofReal (RootDensities.pi (decode ⟨e.val, hv⟩) v) ≤
      ∑' w, ENNReal.ofReal ((config e).c v w) :=
    ofReal_tsum_le_tsum_ofReal (f := fun w => (config e).c v w) fun w => (config e).c_nonneg v w
  have hpiStar : ENNReal.ofReal (RootDensities.piStar (decode ⟨e.val, hv⟩) v) ≤
      ∑' w, ENNReal.ofReal ((config e).c v w)⁻¹ :=
    ofReal_tsum_le_tsum_ofReal (f := fun w => ((config e).c v w)⁻¹)
      fun w => inv_nonneg.2 ((config e).c_nonneg v w)
  unfold RootDensities.finiteEnergyDensity finiteEnergyDensity
  exact mul_le_mul' le_rfl (add_le_add hpi hpiStar)

/-- The rooted (FE) integrands compare the same way, at every point. -/
theorem rootedFiniteEnergyDensity_decode_le (e : EnvGeneral) (hv : Valid e.val) (z : Plane) :
    RootDensities.rootedFiniteEnergyDensity (decode ⟨e.val, hv⟩) z ≤
      rootedFiniteEnergyDensity (config e) z := by
  have hroot : RootDensities.rootAt (decode ⟨e.val, hv⟩) z =
      RootDensities.rootAt (config e).cellsOnly z := rootAt_eq_of_cell_eq rfl z
  unfold RootDensities.rootedFiniteEnergyDensity rootedFiniteEnergyDensity
  rw [hroot]
  cases RootDensities.rootAt (config e).cellsOnly z with
  | none => exact le_rfl
  | some v => exact finiteEnergyDensity_decode_le e hv v

include hA in
/-- **The (FE) moment transfers** from the general law to the lifted valid law. -/
theorem finiteEnergyMoment_validLaw (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val)
    (hV : EnvironmentLaws.SupportedOnValid P) (hFE : FiniteEnergyMoment (generalLaw P hP)) :
    HarmonicLawIngredients.FiniteEnergyMoment (EnvironmentLaws.validLaw P hV) := by
  classical
  show (∫⁻ e, RootDensities.rootedFiniteEnergyDensity (decode e) 0
    ∂EnvironmentLaws.validLaw P hV) < ∞
  rw [lintegral_validLaw_eq P hP hA hfin hV
    RootedFiniteEnergyDensityMeasurable.measurable_rootedFiniteEnergyDensity_zero]
  refine lt_of_le_of_lt (lintegral_mono fun e => ?_) hFE
  by_cases he : FiniteRows e.val
  · rw [dif_pos he]
    exact rootedFiniteEnergyDensity_decode_le e (hA e.val e.property he) 0
  · rw [dif_neg he]
    exact zero_le ..

/-! ### Ergodicity -/

include hA in
/-- **Ergodicity modulo scaling transfers** from the general law to the lifted valid law. -/
theorem environmentErgodic_validLaw (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val)
    (hV : EnvironmentLaws.SupportedOnValid P) (herg : EnvironmentErgodic (generalLaw P hP)) :
    EnvironmentLaws.EnvironmentErgodic (EnvironmentLaws.validLaw P hV) := by
  intro A hAm hAinv
  obtain ⟨B, hB, rfl⟩ := hAm
  have hA'm : MeasurableSet {e : EnvGeneral | FiniteRows e.val ∧ e.val ∈ B} :=
    measurable_subtype_coe (measurableSet_finiteRows.inter hB)
  have hA'inv : SimilarityInvariant {e : EnvGeneral | FiniteRows e.val ∧ e.val ∈ B} := by
    intro s u hs e e' hsim
    show (FiniteRows e.val ∧ e.val ∈ B) ↔ (FiniteRows e'.val ∧ e'.val ∈ B)
    have hiff := finiteRows_iff_of_isSimilarity hsim
    by_cases he : FiniteRows e.val
    · have he' : FiniteRows e'.val := hiff.1 he
      have hB' := hAinv s u hs _ _ (isSimilarity_envOfFiniteRows hA hsim he he')
      exact ⟨fun h => ⟨he', hB'.1 h.2⟩, fun h => ⟨he, hB'.2 h.2⟩⟩
    · have he' : ¬ FiniteRows e'.val := fun h => he (hiff.2 h)
      exact ⟨fun h => absurd h.1 he, fun h => absurd h.1 he'⟩
  have h1 : EnvironmentLaws.validLaw P hV (Subtype.val ⁻¹' B) = P B := by
    rw [← Measure.map_apply measurable_subtype_coe hB, EnvironmentLaws.map_validLaw]
  have h2 : generalLaw P hP (Subtype.val ⁻¹' B) = P B := by
    rw [← Measure.map_apply measurable_subtype_coe hB, map_generalLaw]
  have h3 : generalLaw P hP (Subtype.val ⁻¹' B) =
      generalLaw P hP {e : EnvGeneral | FiniteRows e.val ∧ e.val ∈ B} := by
    refine measure_congr ?_
    filter_upwards [hfin] with e he
    show (e.val ∈ B) = (FiniteRows e.val ∧ e.val ∈ B)
    exact propext ⟨fun h => ⟨he, h⟩, fun h => h.2⟩
  rw [h1, ← h2, h3]
  exact herg _ hA'm hA'inv

end Laws

/-! ### Specializations at the proved adapter `Code.valid_of_validGeneral`

Only Lemma 2.5 (`hfin`) remains a hypothesis. The conclusions are stated in the exact shape of the
earlier main theorems' hypotheses (`AmbientMassTransport`, `FiniteEnergyMoment (validLaw …)`,
`AmbientEnvironmentErgodic`), for an arbitrary proof `hV` of `SupportedOnValid P`. -/

section Specialized

variable (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValidGeneral P)
  (hfin : ∀ᵐ e ∂generalLaw P hP, FiniteRows e.val)

include hfin in
/-- The raw law is carried by `Code.Valid`, from Lemma 2.5 alone. -/
theorem supportedOnValid_of_generalLaw : EnvironmentLaws.SupportedOnValid P :=
  supportedOnValid_of_ae_finiteRows P hP (fun _ h hf => valid_of_validGeneral h hf) hfin

include hfin in
/-- (1.4) under the general law gives the earlier `AmbientMassTransport`. -/
theorem ambientMassTransport_of_generalLaw (hV : EnvironmentLaws.SupportedOnValid P)
    (hMT : MassTransport (generalLaw P hP)) : EnvironmentLaws.AmbientMassTransport P hV :=
  massTransport_validLaw P hP (fun _ h hf => valid_of_validGeneral h hf) hfin hV hMT

include hfin in
/-- (FE) under the general law (extended sums) gives the earlier (FE) moment of `validLaw`. -/
theorem finiteEnergyMoment_validLaw_of_generalLaw (hV : EnvironmentLaws.SupportedOnValid P)
    (hFE : FiniteEnergyMoment (generalLaw P hP)) :
    HarmonicLawIngredients.FiniteEnergyMoment (EnvironmentLaws.validLaw P hV) :=
  finiteEnergyMoment_validLaw P hP (fun _ h hf => valid_of_validGeneral h hf) hfin hV hFE

include hfin in
/-- Ergodicity under the general law gives the earlier `AmbientEnvironmentErgodic`. -/
theorem ambientEnvironmentErgodic_of_generalLaw (hV : EnvironmentLaws.SupportedOnValid P)
    (herg : EnvironmentErgodic (generalLaw P hP)) :
    EnvironmentLaws.AmbientEnvironmentErgodic P hV :=
  environmentErgodic_validLaw P hP (fun _ h hf => valid_of_validGeneral h hf) hfin hV herg

end Specialized

end GeneralLaws

end ReflectedGMS

assert_no_sorry ReflectedGMS.GeneralLaws.measurableSet_finiteRows
assert_no_sorry ReflectedGMS.GeneralLaws.finiteRows_iff_of_isSimilarity
assert_no_sorry ReflectedGMS.GeneralLaws.isSimilarity_envOfFiniteRows
assert_no_sorry ReflectedGMS.GeneralLaws.supportedOnValid_of_ae_finiteRows
assert_no_sorry ReflectedGMS.GeneralLaws.lintegral_validLaw_eq
assert_no_sorry ReflectedGMS.GeneralLaws.extendedKernel
assert_no_sorry ReflectedGMS.GeneralLaws.massTransport_validLaw
assert_no_sorry ReflectedGMS.GeneralLaws.finiteEnergyMoment_validLaw
assert_no_sorry ReflectedGMS.GeneralLaws.environmentErgodic_validLaw
assert_no_sorry ReflectedGMS.GeneralLaws.supportedOnValid_of_generalLaw
assert_no_sorry ReflectedGMS.GeneralLaws.ambientMassTransport_of_generalLaw
assert_no_sorry ReflectedGMS.GeneralLaws.finiteEnergyMoment_validLaw_of_generalLaw
assert_no_sorry ReflectedGMS.GeneralLaws.ambientEnvironmentErgodic_of_generalLaw

#print axioms ReflectedGMS.GeneralLaws.supportedOnValid_of_ae_finiteRows
#print axioms ReflectedGMS.GeneralLaws.lintegral_validLaw_eq
#print axioms ReflectedGMS.GeneralLaws.massTransport_validLaw
#print axioms ReflectedGMS.GeneralLaws.finiteEnergyMoment_validLaw
#print axioms ReflectedGMS.GeneralLaws.environmentErgodic_validLaw
#print axioms ReflectedGMS.GeneralLaws.supportedOnValid_of_generalLaw
#print axioms ReflectedGMS.GeneralLaws.ambientMassTransport_of_generalLaw
#print axioms ReflectedGMS.GeneralLaws.finiteEnergyMoment_validLaw_of_generalLaw
#print axioms ReflectedGMS.GeneralLaws.ambientEnvironmentErgodic_of_generalLaw
