/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Field.Symmetry at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable), and eLpNorm_eq_lintegral_rpow_enorm_toReal takes the measurability hypothesis. -/
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandFacts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Similarity symmetries of the white noise (packet P-X2, target T1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1) and §3.1 (similarity); planning audits
HA5 Details D14 (DGZ Lemma 2.2(2), (4), Lemma 2.5), HA2 Details D2 (Lemma D2.2) and HA4 Details
D2 ("law invariance") and D7.

For a similarity `T z = x₀ + r • O z` (`r > 0`, `O` a linear isometry of `ℝ^d`) the space-time
map `(t, y) ↦ (t / r, T⁻¹ y)` pushes Lebesgue measure on `ℝ × ℝ^d` to `r^{d+1}` times Lebesgue
measure (`map_simST`), so
`(V_T f)(t, y) := r^{-(d+1)/2} f(t / r, T⁻¹ y)`
is a linear isometry of `WN d = L²(ℝ × ℝ^d)` (`simL2ᵢ`). Its inverse is `V_{T⁻¹}`
(`simL2ᵢ_simL2ᵢ_inv`), so it is a linear isometry equivalence (`simL2`). Substituting and using
radiality of `κ`:

* `simFun_bandKernel`, `bandVec_sim`: `k_{a,b,Tz} = V_T k_{a/r,b/r,z}` for `0 < a` (any `b`);
* `IsWhiteNoise.comp_linearIsometry`, `IsWhiteNoise.comp_simL2`: `W ∘ V_T` is a white noise;
* `IsBandVersion.comp_sim`: if `H` is a continuous version of `H_{a,b}` for `W`, then
  `z ↦ H(Tz)` is a continuous version of `H_{a/r,b/r}` for the white noise `W ∘ V_T`; the special
  cases `IsBandVersion.comp_isometry` (`r = 1`) and `IsBandVersion.comp_smul` (`T z = r • z`).

Also: `coeFn_simL2` (the formula for `V_T`), `simL2_symm_apply` (`V_T⁻¹ = V_{T⁻¹}`) and
`sim_comp` (composition of similarities, for recursive frames).

The law identities (`H_{a,b} ∘ T =ᵈ H_{a/r,b/r}` jointly over bands and points) are in
`HigherDimLFPP/Field/SymmetryLaw.lean`.

Template: `LQGMetric.DG.wnScale` (`LQGMetric/Papers/DG/S3D105Sc1.lean`, the planar scaling
isometry `δ⁻² f(δ⁻² s, δ⁻¹(w − b))`), with `ℂ` replaced by `ℝ^d`, the time dilation `δ²` by `r`
and a rotation `O` added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace HigherDimLFPP

variable {d : ℕ}

/-! ### The space-time map -/

/-- The space-time map `(t, y) ↦ (t / r, T⁻¹ y)` of the similarity `T z = x₀ + r • O z`. -/
def simST (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) (p : ℝ × Rd d) : ℝ × Rd d :=
  (r⁻¹ * p.1, r⁻¹ • O.symm (p.2 - x₀))

theorem measurable_simST (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) :
    Measurable (simST O x₀ r) := by
  unfold simST; fun_prop

/-- **Change of variables**: the space-time map pushes Lebesgue measure to `r^{d+1}` times
Lebesgue measure. -/
theorem map_simST (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) :
    Measure.map (simST O x₀ r) volume =
      ENNReal.ofReal (r ^ (d + 1)) • (volume : Measure (ℝ × Rd d)) := by
  have e : simST O x₀ r = Prod.map (fun t : ℝ => r⁻¹ * t)
      ((fun y : Rd d => r⁻¹ • y) ∘ (fun y => O.symm y) ∘ fun y => y - x₀) := by
    funext p; simp only [simST, Prod.map, Function.comp_apply]
  have h1 : Measure.map (fun t : ℝ => r⁻¹ * t) volume =
      ENNReal.ofReal r • (volume : Measure ℝ) := by
    rw [Real.map_volume_mul_left (by positivity), inv_inv, abs_of_pos hr]
  have h2 : Measure.map ((fun y : Rd d => r⁻¹ • y) ∘ (fun y => O.symm y) ∘ fun y => y - x₀)
      volume = ENNReal.ofReal (r ^ d) • (volume : Measure (Rd d)) := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), map_sub_right_eq_self,
      (O.symm.measurePreserving).map_eq,
      Measure.map_addHaar_smul _ (by positivity : (r⁻¹ : ℝ) ≠ 0), finrank_euclideanSpace_fin,
      inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [e, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h1, h2,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul hr.le]
  congr 2
  ring

theorem lintegral_comp_simST (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {g : ℝ × Rd d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g (simST O x₀ r p) = ENNReal.ofReal (r ^ (d + 1)) * ∫⁻ p, g p := by
  rw [← lintegral_map hg (measurable_simST O x₀ r), map_simST O x₀ hr, lintegral_smul_measure]
  rfl

theorem qmp_simST (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (simST O x₀ r) volume volume :=
  ⟨measurable_simST O x₀ r, by rw [map_simST O x₀ hr]; exact Measure.smul_absolutelyContinuous⟩

/-! ### `V_T` on functions -/

/-- `V_T` on functions: `(V_T u)(t, y) = r^{-(d+1)/2} u(t / r, T⁻¹ y)`. -/
def simFun (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) (u : ℝ × Rd d → ℝ) (p : ℝ × Rd d) : ℝ :=
  r ^ (-((d : ℝ) + 1) / 2) * u (simST O x₀ r p)

theorem simFun_congr (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {u v : ℝ × Rd d → ℝ} (huv : u =ᵐ[volume] v) :
    simFun O x₀ r u =ᵐ[volume] simFun O x₀ r v := by
  filter_upwards [(qmp_simST O x₀ hr).ae_eq_comp huv] with p hp
  simp only [simFun]
  rw [show u (simST O x₀ r p) = v (simST O x₀ r p) from hp]

/-- The scalar factor: `(r^{-(d+1)/2})² r^{d+1} = 1`. -/
theorem sim_rpow_sq_mul_pow {r : ℝ} (hr : 0 < r) :
    (r ^ (-((d : ℝ) + 1) / 2)) ^ 2 * r ^ (d + 1) = 1 := by
  rw [← Real.rpow_natCast (r ^ (-((d : ℝ) + 1) / 2)) 2, ← Real.rpow_mul hr.le,
    ← Real.rpow_natCast r (d + 1), ← Real.rpow_add hr]
  have e : -((d : ℝ) + 1) / 2 * ((2 : ℕ) : ℝ) + ((d + 1 : ℕ) : ℝ) = 0 := by
    push_cast; ring
  rw [e, Real.rpow_zero]

theorem lintegral_simFun (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {u : ℝ × Rd d → ℝ} (hu : Measurable u) :
    ∫⁻ p, ‖simFun O x₀ r u p‖ₑ ^ (2 : ℝ) = ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) := by
  set s : ℝ := r ^ (-((d : ℝ) + 1) / 2) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hr.le _
  have e : ∀ p, ‖simFun O x₀ r u p‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (s ^ 2) * ‖u (simST O x₀ r p)‖ₑ ^ (2 : ℝ) := by
    intro p
    rw [simFun, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      Real.enorm_of_nonneg hs0, ENNReal.rpow_two, ← ENNReal.ofReal_pow hs0]
  simp_rw [e]
  rw [lintegral_const_mul _ (show Measurable fun p => ‖u (simST O x₀ r p)‖ₑ ^ (2 : ℝ) from
      (hu.comp (measurable_simST O x₀ r)).enorm.pow_const (2 : ℝ)),
    lintegral_comp_simST O x₀ hr (hu.enorm.pow_const _), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), hs, sim_rpow_sq_mul_pow hr, ENNReal.ofReal_one,
    one_mul]

theorem eLpNorm_simFun (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {u : ℝ × Rd d → ℝ} (hu : AEStronglyMeasurable u volume) :
    eLpNorm (simFun O x₀ r u) 2 volume = eLpNorm u 2 volume := by
  have hv := hu.ae_eq_mk
  rw [eLpNorm_congr_ae (simFun_congr O x₀ hr hv), eLpNorm_congr_ae hv,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    lintegral_simFun O x₀ hr hu.stronglyMeasurable_mk.measurable]
  all_goals first
    | exact hu.stronglyMeasurable_mk.aestronglyMeasurable
    | exact (hu.stronglyMeasurable_mk.aestronglyMeasurable.comp_quasiMeasurePreserving
        (qmp_simST O x₀ hr)).const_mul _

theorem memLp_simFun (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {u : ℝ × Rd d → ℝ} (hu : MemLp u 2 volume) : MemLp (simFun O x₀ r u) 2 volume := by
  rw [memLp_iff, eLpNorm_simFun O x₀ hr hu.aestronglyMeasurable]
  exact hu

/-! ### `V_T` on `WN d` -/

/-- `V_T` on `WN d`. -/
def simL2Fun (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (g : WN d) : WN d :=
  (memLp_simFun O x₀ hr (Lp.memLp g)).toLp _

theorem coeFn_simL2Fun (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (g : WN d) :
    (simL2Fun O x₀ hr g : ℝ × Rd d → ℝ) =ᵐ[volume] simFun O x₀ r g :=
  MemLp.coeFn_toLp _

theorem simL2Fun_add (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (f g : WN d) :
    simL2Fun O x₀ hr (f + g) = simL2Fun O x₀ hr f + simL2Fun O x₀ hr g := by
  apply Lp.ext
  filter_upwards [coeFn_simL2Fun O x₀ hr (f + g), coeFn_simL2Fun O x₀ hr f,
    coeFn_simL2Fun O x₀ hr g, Lp.coeFn_add (simL2Fun O x₀ hr f) (simL2Fun O x₀ hr g),
    simFun_congr O x₀ hr (Lp.coeFn_add f g)] with p h1 h2 h3 h4 h5
  rw [h4, h1, h5, Pi.add_apply, h2, h3]
  simp only [simFun, Pi.add_apply, mul_add]

theorem simL2Fun_smul (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (c : ℝ)
    (g : WN d) : simL2Fun O x₀ hr (c • g) = c • simL2Fun O x₀ hr g := by
  apply Lp.ext
  filter_upwards [coeFn_simL2Fun O x₀ hr (c • g), coeFn_simL2Fun O x₀ hr g,
    Lp.coeFn_smul c (simL2Fun O x₀ hr g), simFun_congr O x₀ hr (Lp.coeFn_smul c g)]
    with p h1 h2 h4 h5
  rw [h4, h1, h5, Pi.smul_apply, h2]
  simp only [simFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The similarity isometry** `(V_T f)(t, y) = r^{-(d+1)/2} f(t / r, T⁻¹ y)` of
`WN d = L²(ℝ × ℝ^d)`, for `T z = x₀ + r • O z`. -/
def simL2ᵢ (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) : WN d →ₗᵢ[ℝ] WN d where
  toFun := simL2Fun O x₀ hr
  map_add' := simL2Fun_add O x₀ hr
  map_smul' := simL2Fun_smul O x₀ hr
  norm_map' g := by
    show ‖simL2Fun O x₀ hr g‖ = ‖g‖
    rw [simL2Fun, Lp.norm_toLp, eLpNorm_simFun O x₀ hr (Lp.aestronglyMeasurable g), Lp.norm_def]

theorem coeFn_simL2ᵢ (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (g : WN d) :
    (simL2ᵢ O x₀ hr g : ℝ × Rd d → ℝ) =ᵐ[volume] simFun O x₀ r g :=
  coeFn_simL2Fun O x₀ hr g

/-- `V_T` on an explicit square-integrable kernel. -/
theorem simL2ᵢ_toLp (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {u : ℝ × Rd d → ℝ} (hu : MemLp u 2 volume) :
    simL2ᵢ O x₀ hr (hu.toLp u) = (memLp_simFun O x₀ hr hu).toLp _ := by
  apply Lp.ext
  filter_upwards [coeFn_simL2ᵢ O x₀ hr (hu.toLp u), simFun_congr O x₀ hr hu.coeFn_toLp,
    (memLp_simFun O x₀ hr hu).coeFn_toLp] with p h1 h2 h3
  rw [h1, h2, h3]

/-! ### The inverse similarity -/

/-- The translation part `x₀' = -r⁻¹ O⁻¹ x₀` of the inverse similarity
`T⁻¹ w = x₀' + r⁻¹ • O⁻¹ w`. -/
def simInvShift (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) (r : ℝ) : Rd d := -(r⁻¹ • O.symm x₀)

/-- The space-time map of `T⁻¹` inverts the space-time map of `T`. -/
theorem simST_inv_simST (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    (p : ℝ × Rd d) : simST O.symm (simInvShift O x₀ r) r⁻¹ (simST O x₀ r p) = p := by
  have hr0 : r ≠ 0 := hr.ne'
  obtain ⟨t, y⟩ := p
  refine Prod.ext ?_ ?_
  · simp only [simST, inv_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  · simp only [simST, simInvShift, inv_inv, LinearIsometryEquiv.symm_symm, sub_neg_eq_add,
      map_add, map_smul, LinearIsometryEquiv.apply_symm_apply, smul_add, smul_smul,
      mul_inv_cancel₀ hr0, one_smul]
    abel

/-- The scalar factors of `V_T` and `V_{T⁻¹}` are inverse to each other. -/
theorem sim_rpow_mul_inv_rpow {r : ℝ} (hr : 0 < r) :
    r ^ (-((d : ℝ) + 1) / 2) * r⁻¹ ^ (-((d : ℝ) + 1) / 2) = 1 := by
  rw [Real.inv_rpow hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne']

/-- `V_T ∘ V_{T⁻¹} = id`. -/
theorem simL2ᵢ_simL2ᵢ_inv (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (f : WN d) :
    simL2ᵢ O x₀ hr (simL2ᵢ O.symm (simInvShift O x₀ r) (inv_pos.2 hr) f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_simL2ᵢ O x₀ hr (simL2ᵢ O.symm (simInvShift O x₀ r) (inv_pos.2 hr) f),
    simFun_congr O x₀ hr (coeFn_simL2ᵢ O.symm (simInvShift O x₀ r) (inv_pos.2 hr) f)]
    with p h1 h2
  rw [h1, h2]
  simp only [simFun]
  rw [simST_inv_simST O x₀ hr p, ← mul_assoc, sim_rpow_mul_inv_rpow hr, one_mul]

theorem surjective_simL2ᵢ (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) :
    Function.Surjective (simL2ᵢ O x₀ hr) := fun f =>
  ⟨_, simL2ᵢ_simL2ᵢ_inv O x₀ hr f⟩

/-- **The unitary `V_T`** (target T1): the similarity isometry as a linear isometry equivalence
of `WN d`, for `T z = x₀ + r • O z`, `r > 0`. -/
def simL2 (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) : WN d ≃ₗᵢ[ℝ] WN d :=
  LinearIsometryEquiv.ofSurjective (simL2ᵢ O x₀ hr) (surjective_simL2ᵢ O x₀ hr)

@[simp]
theorem simL2_apply (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r) (f : WN d) :
    simL2 O x₀ hr f = simL2ᵢ O x₀ hr f :=
  rfl

/-! ### Band vectors -/

variable {κ : Rd d → ℝ}

/-- The spatial argument of the kernel identity. -/
theorem simST_arg (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ z y : Rd d) {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    (r⁻¹ * t)⁻¹ • (z - r⁻¹ • O.symm (y - x₀)) = O.symm (t⁻¹ • (x₀ + r • O z - y)) := by
  rw [mul_inv, inv_inv, mul_comm, mul_smul, smul_sub, smul_smul r r⁻¹, mul_inv_cancel₀ hr,
    one_smul]
  simp only [map_smul, map_sub, map_add, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  abel

/-- **Kernel identity**: `r^{-(d+1)/2} k_{a/r,b/r,z}(t/r, T⁻¹ y) = k_{a,b,Tz}(t, y)` for
`0 < a` (substitution and radiality of `κ`). -/
theorem simFun_bandKernel (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ}
    (hr : 0 < r) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    simFun O x₀ r (bandKernel κ (a / r) (b / r) z) = bandKernel κ a b (x₀ + r • O z) := by
  funext p
  obtain ⟨t, y⟩ := p
  have hmem : r⁻¹ * t ∈ Ioo (a / r) (b / r) ↔ t ∈ Ioo a b := by
    simp only [mem_Ioo, inv_mul_eq_div, div_lt_div_iff_of_pos_right hr]
  simp only [simFun, simST, bandKernel]
  by_cases ht : t ∈ Ioo a b
  · have ht0 : 0 < t := lt_trans ha ht.1
    rw [indicator_of_mem (hmem.2 ht), indicator_of_mem ht]
    simp only [scaleKernel]
    rw [simST_arg O x₀ z y hr.ne', hκ.comp_linearIsometryEquiv O.symm,
      Real.mul_rpow (inv_nonneg.2 hr.le) ht0.le, ← mul_assoc, ← mul_assoc,
      sim_rpow_mul_inv_rpow hr, one_mul]
  · rw [indicator_of_notMem (fun h => ht (hmem.1 h)), indicator_of_notMem ht, mul_zero]

/-- **Band vectors under similarities** (target T1): `k_{a,b,Tz} = V_T k_{a/r,b/r,z}` for
`T z = x₀ + r • O z`, `0 < a` and every `b`, `z`. -/
theorem bandVec_sim (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ}
    (hr : 0 < r) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    bandVec κ a b (x₀ + r • O z) = simL2 O x₀ hr (bandVec κ (a / r) (b / r) z) := by
  rw [simL2_apply, bandVec_eq_toLp hκ (div_pos ha hr), simL2ᵢ_toLp, bandVec_eq_toLp hκ ha]
  exact MemLp.toLp_congr _ _
    (Eventually.of_forall fun p => (congrFun (simFun_bandKernel hκ O x₀ hr ha b z) p).symm)

/-! ### White noise and versions -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- `W ∘ V` is a white noise for every linear isometry `V` of `WN d`. -/
theorem IsWhiteNoise.comp_linearIsometry (hW : IsWhiteNoise P W) (V : WN d →ₗᵢ[ℝ] WN d) :
    IsWhiteNoise P (fun f => W (V f)) := by
  refine ⟨fun f => hW.measurable _, fun {ι} _ f c => ?_⟩
  have h := hW.hasLaw (fun i => V (f i)) c
  have e : ‖∑ i, c i • V (f i)‖ = ‖∑ i, c i • f i‖ := by
    rw [← V.norm_map (∑ i, c i • f i), map_sum]
    simp only [LinearIsometry.map_smul]
  rw [e] at h
  exact h

/-- `W ∘ V` is a white noise for every linear isometry equivalence `V` of `WN d`. -/
theorem IsWhiteNoise.comp_linearIsometryEquiv (hW : IsWhiteNoise P W)
    (V : WN d ≃ₗᵢ[ℝ] WN d) : IsWhiteNoise P (fun f => W (V f)) :=
  hW.comp_linearIsometry V.toLinearIsometry

/-- **`W ∘ V_T` is a white noise** (target T1). -/
theorem IsWhiteNoise.comp_simL2 (hW : IsWhiteNoise P W) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d)
    {r : ℝ} (hr : 0 < r) : IsWhiteNoise P (fun f => W (simL2 O x₀ hr f)) :=
  hW.comp_linearIsometryEquiv (simL2 O x₀ hr)

/-- **Versions under similarities** (target T1): if `H` is a continuous version of `H_{a,b}` for
`W`, then `z ↦ H(x₀ + r • O z)` is a continuous version of `H_{a/r,b/r}` for the white noise
`W ∘ V_T`. -/
theorem IsBandVersion.comp_sim {a b : ℝ} {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    (hκ : IsLFPPKernel κ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    (ha : 0 < a) :
    IsBandVersion P (fun f => W (simL2 O x₀ hr f)) κ (a / r) (b / r)
      (fun z => H (x₀ + r • O z)) where
  continuous ω := (hH.continuous ω).comp (continuous_const.add (O.continuous.const_smul r))
  measurable z := hH.measurable _
  ae_eq z := by
    show H (x₀ + r • O z) =ᵐ[P] W (simL2 O x₀ hr (bandVec κ (a / r) (b / r) z))
    rw [← bandVec_sim hκ O x₀ hr ha b z]
    exact hH.ae_eq _

end HigherDimLFPP
