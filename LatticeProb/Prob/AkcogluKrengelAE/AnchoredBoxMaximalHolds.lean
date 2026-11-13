import LatticeProb.Prob.AkcogluKrengelAE.BoxTiling
import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxMean
import LatticeProb.Prob.AkcogluKrengelAE.BirkhoffLpMaximalProved

/-!
# The `Lᵖ` maximal inequality for anchored boxes

For `p > 1`, a measure-preserving additive `ℤᵈ`-action `σ` and a measurable `f ≥ 0`, the maximal
function `sup_m` of the averages of `f` over the boxes `∏_{i ∈ s} [0, mᵢ)` has `Lᵖ` norm at most a
constant times that of `f`.  The box average over `insert i s` is the Birkhoff average along
`σ (unit i)` of the box average over `s` (`boxAvg_insert_eq_bAvg_boxAvg`), so the box maximal
function over `insert i s` is dominated by the one-parameter maximal function of the box maximal
function over `s`; Wiener's maximal theorem `birkhoffLpMaximal`, applied once per coordinate,
gives the bound.  The anchored box `∏ᵢ [0, ⌈N cᵢ⌉)` has volume at most a constant times `Nᵈ`, which
gives the centred anchored-box maximal inequality `AnchoredBoxMaximalCentred` for every `p > 1`.

## Main results

* `exists_lintegral_iSup_boxAvg_rpow_le`: the `Lᵖ` box maximal inequality;
* `anchoredBoxMaximalCentred_holds`: `AnchoredBoxMaximalCentred d c p` for `p > 1`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {d : ℕ}

/-- Box averages of a nonnegative function are nonnegative. -/
theorem boxAvg_nonneg {Ω : Type*} [MeasurableSpace Ω] {σ : Site d → Ω → Ω} {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (s : Finset (Fin d)) (m : Fin d → ℕ) (ω : Ω) : 0 ≤ boxAvg σ f s m ω := by
  unfold boxAvg
  exact div_nonneg (Finset.sum_nonneg fun _ _ => hf0 _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- A Birkhoff average of a nonnegative function, read in `ℝ≥0∞`, is at most the `ℝ≥0∞` average of
any upper bound of the function. -/
theorem ofReal_bAvg_le {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω} {F : Ω → ℝ}
    (hF : ∀ ω, 0 ≤ F ω) (G : Ω → ℝ≥0∞) (hFG : ∀ ω, ENNReal.ofReal (F ω) ≤ G ω) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (bAvg T F n ω) ≤ (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n, G (T^[k] ω) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bAvg]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [bAvg, birkhoffSum, ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg fun k _ => hF _, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_right (Finset.sum_le_sum fun k _ => hFG _) _

/-- **The `Lᵖ` box maximal inequality.**  For `p > 1` and `s : Finset (Fin d)` there is `C ≥ 0`
with `∫⁻ (sup_m boxAvg σ f s m)ᵖ ≤ C ∫⁻ fᵖ` for every measurable `f ≥ 0`. -/
theorem exists_lintegral_iSup_boxAvg_rpow_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : Site d → Ω → Ω} (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) {p : ℝ} (hp : 1 < p) (s : Finset (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Ω → ℝ, Measurable f → (∀ ω, 0 ≤ f ω) →
      ∫⁻ ω, (⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f s m ω)) ^ p ∂μ ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂μ := by
  obtain ⟨C₁, hC₁, hB⟩ := birkhoffLpMaximal p hp
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, zero_le_one, fun f hf _ => ?_⟩
    simp only [boxAvg_empty, ciSup_const, ENNReal.ofReal_one, one_mul]
    have hm : Measurable fun ω => ENNReal.ofReal (f ω) ^ p := hf.ennreal_ofReal.pow_const p
    exact ((hσ (natToSite 0)).lintegral_comp hm).le
  | @insert i s hi ih =>
    obtain ⟨C, hC, hs⟩ := ih
    refine ⟨C₁ * C, mul_nonneg hC₁ hC, fun f hf hf0 => ?_⟩
    let G : Ω → ℝ≥0∞ := fun ω => ⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f s m ω)
    have hGm : Measurable G :=
      Measurable.iSup fun m => (measurable_boxAvg hσ hf s m).ennreal_ofReal
    have hle : ∀ ω, (⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f (insert i s) m ω)) ≤
        ⨆ n : ℕ, (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n, G ((σ (unit i))^[k] ω) := by
      intro ω
      refine iSup_le fun m => ?_
      rw [boxAvg_insert_eq_bAvg_boxAvg hσadd f s i hi m ω]
      refine (ofReal_bAvg_le (boxAvg_nonneg hf0 s m) G
        (fun ω' => le_iSup (fun m' : Fin d → ℕ => ENNReal.ofReal (boxAvg σ f s m' ω')) m)
        (m i) ω).trans ?_
      exact le_iSup (fun n : ℕ => (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n,
        G ((σ (unit i))^[k] ω)) (m i)
    calc ∫⁻ ω, (⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg σ f (insert i s) m ω)) ^ p ∂μ
        ≤ ∫⁻ ω, (⨆ n : ℕ, (n : ℝ≥0∞)⁻¹ *
            ∑ k ∈ Finset.range n, G ((σ (unit i))^[k] ω)) ^ p ∂μ :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow (hle ω) (by linarith)
      _ ≤ ENNReal.ofReal C₁ * ∫⁻ ω, G ω ^ p ∂μ := hB μ inferInstance (σ (unit i)) (hσ _) G hGm
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂μ) :=
          mul_le_mul_right (hs f hf hf0) _
      _ = ENNReal.ofReal (C₁ * C) * ∫⁻ ω, ENNReal.ofReal (f ω) ^ p ∂μ := by
          rw [ENNReal.ofReal_mul hC₁, mul_assoc]

/-- **The centred anchored-box `Lᵖ` maximal inequality** for `p > 1`. -/
theorem anchoredBoxMaximalCentred_holds (c : Fin d → ℝ) {p : ℝ} (hp : 1 < p) :
    AnchoredBoxMaximalCentred d c p := by
  intro hc Ω _ μ _ τ hτ hadd
  obtain ⟨C, hC, hbox⟩ := exists_lintegral_iSup_boxAvg_rpow_le hτ hadd hp Finset.univ
  obtain ⟨K, hK⟩ := (tendsto_prod_ceil_toNat_div_pow hc).bddAbove_range
  have hK' : 0 ≤ max K 0 := le_max_right _ _
  have hp0 : 0 ≤ p := by linarith
  refine ⟨max K 0 ^ p * C, mul_nonneg (Real.rpow_nonneg hK' _) hC, fun h hh _ => ?_⟩
  let g : Ω → ℝ := fun ω => h ω - ∫ x, h x ∂μ
  have hgm : Measurable g := hh.sub_const _
  let B : Ω → ℝ≥0∞ := fun ω =>
    ⨆ m : Fin d → ℕ, ENNReal.ofReal (boxAvg τ (fun ω => |g ω|) Finset.univ m ω)
  have hpt : ∀ ω, (⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgMean g τ c N ω|) ≤
      ENNReal.ofReal (max K 0) * B ω := by
    intro ω
    refine iSup_le fun N => ?_
    have hsum : ∑ x ∈ anchoredBox c N, |g (τ x ω)| =
        boxAvg τ (fun ω => |g ω|) Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω *
          ∏ i, ((⌈(N : ℝ) * c i⌉.toNat : ℕ) : ℝ) := by
      rw [anchoredBox_eq_intBox hc N,
        ← sum_boxGridSet_eq_sum_intBox Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat)
          (fun x => |g (τ x ω)|),
        sum_boxGridSet_eq_boxAvg_mul τ (fun ω => |g ω|) Finset.univ
          (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω]
    have hscaleN : (N : ℝ) ^ (-(d : ℝ)) * ∏ i, ((⌈(N : ℝ) * c i⌉.toNat : ℕ) : ℝ) ≤ max K 0 := by
      have e : (N : ℝ) ^ (-(d : ℝ)) * ∏ i, ((⌈(N : ℝ) * c i⌉.toNat : ℕ) : ℝ) =
          (∏ i, ((⌈(N : ℝ) * c i⌉.toNat : ℕ) : ℝ)) / (N : ℝ) ^ d := by
        rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, div_eq_mul_inv, mul_comm]
      rw [e]
      exact (hK (Set.mem_range_self N)).trans (le_max_left _ _)
    have hbnn : 0 ≤ boxAvg τ (fun ω => |g ω|) Finset.univ
        (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω := boxAvg_nonneg (fun _ => abs_nonneg _) _ _ _
    have hA : |anchoredBoxAvgMean g τ c N ω| ≤
        max K 0 * boxAvg τ (fun ω => |g ω|) Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω := by
      unfold anchoredBoxAvgMean
      have hpow : 0 ≤ (N : ℝ) ^ (-(d : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      rw [abs_mul, abs_of_nonneg hpow]
      calc (N : ℝ) ^ (-(d : ℝ)) * |∑ x ∈ anchoredBox c N, g (τ x ω)|
          ≤ (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, |g (τ x ω)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hpow
        _ = ((N : ℝ) ^ (-(d : ℝ)) * ∏ i, ((⌈(N : ℝ) * c i⌉.toNat : ℕ) : ℝ)) *
              boxAvg τ (fun ω => |g ω|) Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω := by
            rw [hsum]; ring
        _ ≤ max K 0 * boxAvg τ (fun ω => |g ω|) Finset.univ
              (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω :=
            mul_le_mul_of_nonneg_right hscaleN hbnn
    calc ENNReal.ofReal |anchoredBoxAvgMean g τ c N ω|
        ≤ ENNReal.ofReal (max K 0 * boxAvg τ (fun ω => |g ω|) Finset.univ
            (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω) := ENNReal.ofReal_le_ofReal hA
      _ = ENNReal.ofReal (max K 0) * ENNReal.ofReal (boxAvg τ (fun ω => |g ω|) Finset.univ
            (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω) := ENNReal.ofReal_mul hK'
      _ ≤ ENNReal.ofReal (max K 0) * B ω :=
          mul_le_mul_right (le_iSup (fun m' : Fin d → ℕ =>
            ENNReal.ofReal (boxAvg τ (fun ω => |g ω|) Finset.univ m' ω)) _) _
  have htop : ENNReal.ofReal (max K 0) ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  calc ∫⁻ ω, (⨆ N : ℕ, ENNReal.ofReal |anchoredBoxAvgMean g τ c N ω|) ^ p ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (max K 0) * B ω) ^ p ∂μ :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpt ω) hp0
    _ = ENNReal.ofReal (max K 0) ^ p * ∫⁻ ω, B ω ^ p ∂μ := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact lintegral_const_mul' _ _ htop
    _ ≤ ENNReal.ofReal (max K 0) ^ p *
          (ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal |g ω| ^ p ∂μ) :=
        mul_le_mul_right (hbox (fun ω => |g ω|) (continuous_abs.measurable.comp hgm)
          (fun _ => abs_nonneg _)) _
    _ = ENNReal.ofReal (max K 0 ^ p * C) * ∫⁻ ω, ENNReal.ofReal |g ω| ^ p ∂μ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hK' _),
          ENNReal.ofReal_rpow_of_nonneg hK' hp0, mul_assoc]

end LatticeProb
