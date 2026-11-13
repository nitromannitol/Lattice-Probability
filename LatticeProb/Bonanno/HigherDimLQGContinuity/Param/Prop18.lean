/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGContinuity.Param.Prop18 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGContinuity.Param.Interval

/-!
# The parametrization `γ ↦ ξ` and `prop18_holds` (packet PAR, target A)

Blueprint Part A §1, `a:lem-gamma` and `a:ssec-assembly` ([C] (1.5), l. 74–81; NA1 R1 Step 7). For
`γ ∈ (0, √(2d))`, `Ξ(γ) = xiOfGamma d γ` is the unique `ξ > 0` with `Q(ξ) = G(γ) = d/γ + γ/2`
(`Q⁻¹ ∘ G`, with `Q⁻¹` the inverse of `Q` on the subcritical set), and `Ξ(γ) = 0` otherwise. It is strictly
increasing and continuous on `[0, √(2d))`, maps it onto `xiRange d = [0, ξ_c)`, and
`γ / Ξ(γ) = (d + γ²/2) / ϕ(Ξ(γ)) → d / ϕ(0) = d` as `γ ↓ 0`.

Main statements: `xiOfGamma`, `xiOfGamma_spec`, `distExp_eq_gammaQ_iff`, `xiOfGamma_strictMonoOn`,
`xiOfGamma_image_Ioo`, `xiOfGamma_image_Ico`, `xiOfGamma_continuousOn`, `tendsto_xiOfGamma_zero`,
`tendsto_div_xiOfGamma`, and **`prop18_holds`** (the frozen statement of `prop18`, verbatim).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- `Ξ(γ)`: for `0 < γ < √(2d)` the subcritical `ξ` with `Q(ξ) = d/γ + γ/2` (`Q⁻¹ ∘ G`); `0` otherwise. -/
def xiOfGamma (d : ℕ) (γ : ℝ) : ℝ :=
  if γ ∈ Ioo 0 (Real.sqrt (2 * d)) then
    Function.invFunOn (distExp d) (subcritSet d) (gammaQ d γ)
  else 0

variable {d : ℕ}

theorem xiOfGamma_of_notMem {γ : ℝ} (hγ : γ ∉ Ioo 0 (Real.sqrt (2 * d))) : xiOfGamma d γ = 0 := by
  rw [xiOfGamma, ite_eq_right_of_eq_false _ _ (eq_false hγ)]

@[simp] theorem xiOfGamma_zero (d : ℕ) : xiOfGamma d 0 = 0 :=
  xiOfGamma_of_notMem fun h => lt_irrefl 0 h.1

/-- `Ξ(γ)` is subcritical and `Q(Ξ(γ)) = d/γ + γ/2`. -/
theorem xiOfGamma_spec (hd : 2 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo 0 (Real.sqrt (2 * d))) :
    xiOfGamma d γ ∈ subcritSet d ∧ distExp d (xiOfGamma d γ) = gammaQ d γ := by
  have hex : ∃ ξ ∈ subcritSet d, distExp d ξ = gammaQ d γ :=
    distExp_surjOn hd (sqrt_lt_gammaQ hγ.1 hγ.2)
  rw [xiOfGamma, ite_eq_left_of_eq_true _ _ (eq_true hγ)]
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

theorem xiOfGamma_pos (hd : 2 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo 0 (Real.sqrt (2 * d))) :
    0 < xiOfGamma d γ :=
  (xiOfGamma_spec hd hγ).1.1

/-- **Characterization** of `Ξ`: for `0 < γ < √(2d)` and `ξ > 0`, `Q(ξ) = d/γ + γ/2 ↔ ξ = Ξ(γ)`. -/
theorem distExp_eq_gammaQ_iff (hd : 2 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo 0 (Real.sqrt (2 * d))) {ξ : ℝ}
    (hξ : 0 < ξ) : distExp d ξ = gammaQ d γ ↔ ξ = xiOfGamma d γ := by
  obtain ⟨hmem, heq⟩ := xiOfGamma_spec hd hγ
  constructor
  · intro h
    have hS : ξ ∈ subcritSet d := ⟨hξ, h ▸ sqrt_lt_gammaQ hγ.1 hγ.2⟩
    exact (distExp_strictAntiOn hd).injOn hS hmem (h.trans heq.symm)
  · rintro rfl
    exact heq

/-- `Ξ` is strictly increasing on `[0, √(2d))`. -/
theorem xiOfGamma_strictMonoOn (hd : 2 ≤ d) :
    StrictMonoOn (xiOfGamma d) (Ico 0 (Real.sqrt (2 * d))) := by
  intro a ha b hb hab
  have hb' : b ∈ Ioo 0 (Real.sqrt (2 * d)) := ⟨ha.1.trans_lt hab, hb.2⟩
  obtain ⟨hbS, hbQ⟩ := xiOfGamma_spec hd hb'
  rcases ha.1.lt_or_eq with ha0 | rfl
  · have ha' : a ∈ Ioo 0 (Real.sqrt (2 * d)) := ⟨ha0, ha.2⟩
    obtain ⟨haS, haQ⟩ := xiOfGamma_spec hd ha'
    have hG : gammaQ d b < gammaQ d a := gammaQ_strictAntiOn d ha' hb' hab
    refine lt_of_not_ge fun hle => ?_
    have := (distExp_strictAntiOn hd).antitoneOn hbS haS hle
    linarith
  · rw [xiOfGamma_zero]
    exact hbS.1

/-- `Ξ` maps `(0, √(2d))` onto the subcritical set. -/
theorem xiOfGamma_image_Ioo (hd : 2 ≤ d) :
    xiOfGamma d '' Ioo 0 (Real.sqrt (2 * d)) = subcritSet d := by
  ext ξ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact (xiOfGamma_spec hd hγ).1
  · intro hξ
    obtain ⟨γ, hγ, hG⟩ := exists_gammaQ_eq (by omega) hξ.2
    exact ⟨γ, hγ, ((distExp_eq_gammaQ_iff hd hγ hξ.1).1 hG.symm).symm⟩

/-- `Ξ` maps `[0, √(2d))` onto `xiRange d`. -/
theorem xiOfGamma_image_Ico (hd : 2 ≤ d) :
    xiOfGamma d '' Ico 0 (Real.sqrt (2 * d)) = xiRange d := by
  have hs : (0 : ℝ) < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  rw [← Ioo_insert_left hs, image_insert_eq, xiOfGamma_zero, xiOfGamma_image_Ioo hd,
    xiRange_eq_insert_subcritSet]

/-- `Ξ` is continuous on `[0, √(2d))` (a strictly monotone map whose image is an interval). -/
theorem xiOfGamma_continuousOn (hd : 2 ≤ d) :
    ContinuousOn (xiOfGamma d) (Ico 0 (Real.sqrt (2 * d))) := by
  have hs : (0 : ℝ) < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  intro γ hγ
  rcases hγ.1.lt_or_eq with h0 | rfl
  · have hγ' : γ ∈ Ioo 0 (Real.sqrt (2 * d)) := ⟨h0, hγ.2⟩
    refine (((xiOfGamma_strictMonoOn hd).mono Ioo_subset_Ico_self).continuousAt_of_image_mem_nhds
      (Ioo_mem_nhds h0 hγ.2) ?_).continuousWithinAt
    have hmem := (xiOfGamma_spec hd hγ').1
    rw [subcritSet_eq_Ioo hd] at hmem
    rw [xiOfGamma_image_Ioo hd, subcritSet_eq_Ioo hd]
    exact Ioo_mem_nhds hmem.1 hmem.2
  · refine ((xiOfGamma_strictMonoOn hd).continuousWithinAt_right_of_image_mem_nhdsWithin
      (Ico_mem_nhdsGE hs) ?_).mono Ico_subset_Ici_self
    rw [xiOfGamma_image_Ico hd, xiOfGamma_zero, xiRange_eq_Ico hd]
    exact Ico_mem_nhdsGE (xiCrit_pos hd)

/-- `Ξ(γ) → 0` as `γ ↓ 0`. -/
theorem tendsto_xiOfGamma_zero (hd : 2 ≤ d) :
    Tendsto (xiOfGamma d) (𝓝[>] 0) (𝓝 0) := by
  have hs : (0 : ℝ) < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have h := xiOfGamma_continuousOn hd 0 ⟨le_rfl, hs⟩
  rw [ContinuousWithinAt, xiOfGamma_zero] at h
  exact h.mono_left (nhdsWithin_le_of_mem
    (mem_of_superset (Ioo_mem_nhdsGT hs) Ioo_subset_Ico_self))

/-- `γ / Ξ(γ) → d` as `γ ↓ 0` ([3, Cor. 1.9] for the repository's exponent). -/
theorem tendsto_div_xiOfGamma (hd : 2 ≤ d) :
    Tendsto (fun γ => γ / xiOfGamma d γ) (𝓝[>] 0) (𝓝 (d : ℝ)) := by
  have hs : (0 : ℝ) < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have hφ : Tendsto (fun γ => phiXi d (xiOfGamma d γ)) (𝓝[>] 0) (𝓝 1) := by
    have h := ((phiXi_continuous hd).tendsto 0).comp (tendsto_xiOfGamma_zero hd)
    rwa [phiXi_zero] at h
  have hnum : Tendsto (fun γ : ℝ => (d : ℝ) + γ ^ 2 / 2) (𝓝[>] 0) (𝓝 (d : ℝ)) := by
    have h : Tendsto (fun γ : ℝ => (d : ℝ) + γ ^ 2 / 2) (𝓝 0) (𝓝 ((d : ℝ) + 0 ^ 2 / 2)) :=
      ((continuous_const.add ((continuous_pow 2).div_const 2))).tendsto 0
    simpa using h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have h := hnum.div hφ one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hs] with γ hγ
  obtain ⟨hS, hQ⟩ := xiOfGamma_spec hd hγ
  have hx : 0 < xiOfGamma d γ := hS.1
  have hγ0 : 0 < γ := hγ.1
  rw [Pi.div_apply, phiXi_of_pos hx, hQ, gammaQ]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hne : (d : ℝ) + γ ^ 2 / 2 ≠ 0 := by positivity
  field_simp

/-- **Target A** (the frozen statement of `prop18`, verbatim): the parametrization (1.5). -/
theorem prop18_holds :
    ∀ d : ℕ, 3 ≤ d →
      ContinuousOn (distExp d) (Ioi 0) ∧
      StrictAntiOn (distExp d) {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ} ∧
      Tendsto (fun ξ => ξ * distExp d ξ) (𝓝[>] 0) (𝓝 1) ∧
      ∃ Ξ : ℝ → ℝ, Ξ 0 = 0 ∧
        StrictMonoOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        ContinuousOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        Ξ '' Ico 0 (Real.sqrt (2 * d)) = xiRange d ∧
        (∀ γ ∈ Ioo (0 : ℝ) (Real.sqrt (2 * d)), ∀ ξ : ℝ, 0 < ξ →
          (distExp d ξ = (d : ℝ) / γ + γ / 2 ↔ ξ = Ξ γ)) ∧
        Tendsto (fun γ => γ / Ξ γ) (𝓝[>] 0) (𝓝 (d : ℝ)) := by
  intro d hd
  have hd2 : 2 ≤ d := by omega
  exact ⟨distExp_continuousOn hd2, distExp_strictAntiOn hd2, tendsto_mul_distExp hd2,
    xiOfGamma d, xiOfGamma_zero d, xiOfGamma_strictMonoOn hd2, xiOfGamma_continuousOn hd2,
    xiOfGamma_image_Ico hd2, fun γ hγ ξ hξ => distExp_eq_gammaQ_iff hd2 hγ hξ,
    tendsto_div_xiOfGamma hd2⟩

end HigherDimLQGContinuity
