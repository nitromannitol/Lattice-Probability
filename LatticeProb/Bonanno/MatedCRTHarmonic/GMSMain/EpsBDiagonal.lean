/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBDiagonal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces

/-!
# From dyadic band sequences to every real mesh

[18] states its estimates "for each `ε ∈ (0, 1)`" . The landed [18] layer (the grid annulus-disconnection estimate
`ScaledGridControl`, Lemma 3.8, Lemma 3.11) runs on a `CellFamily.RandomCellFamily` whose `k`-th member is measured
against the dyadic scale `CellFamily.mesh k = 2⁻ᵏ`. re-uses it for a real mesh `θₖ` in the *band*
`(2⁻ᵏ⁻¹, 2⁻ᵏ]`: the `k`-th member of the family is the mesh-`θₖ` map, and every polynomial statement at scale `2⁻ᵏ`
is compared with the same statement at scale `θₖ` (a factor `2`, absorbed by halving exponents). This gives the
real-mesh estimate along *every* band sequence `θ`, but with constants that may depend on `θ`.

This file removes that dependence by a diagonal argument (`uniform_of_bandSeq`): if, for every band sequence, some
member of a countable, monotone family of estimates `Good ε n C` holds along the sequence, then one member holds at
every real `ε ∈ (0, 1)`. Otherwise, for each `m` there are meshes `ε` in arbitrarily fine bands where the `m`-th
estimate with constant `m` fails; choosing one such mesh in a new band for each `m` gives a band sequence along which
no estimate holds. `uniform_rate_of_bandSeq` is the instance for bad-event bounds `b(ε, β, p) ≤ C ε^α` monotone in
`(β, p)` (the shape of [18] Lemma 3.11), `exists_band` locates every `ε ∈ (0, 1)` in its band.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-! ### Dyadic bands -/

theorem mesh_pos (k : ℕ) : 0 < CellFamily.mesh k := zpow_pos (by norm_num) _

theorem mesh_le_one (k : ℕ) : CellFamily.mesh k ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by simp)

theorem mesh_eq_inv_pow (k : ℕ) : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
  simp [CellFamily.mesh, zpow_neg, zpow_natCast]

theorem mesh_succ (k : ℕ) : CellFamily.mesh (k + 1) = CellFamily.mesh k / 2 := by
  rw [mesh_eq_inv_pow, mesh_eq_inv_pow, pow_succ, mul_inv, div_eq_mul_inv]

theorem mesh_antitone : Antitone CellFamily.mesh := by
  intro a b hab
  rw [mesh_eq_inv_pow, mesh_eq_inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hab)

theorem mesh_zero : CellFamily.mesh 0 = 1 := by simp [CellFamily.mesh]

theorem tendsto_mesh : Tendsto CellFamily.mesh atTop (nhds 0) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  convert tendsto_inv_atTop_zero.comp hp using 1
  ext k
  simp [mesh_eq_inv_pow]

/-- **Band sequences.** `θ k` lies in the `k`-th dyadic band `(2⁻ᵏ⁻¹, 2⁻ᵏ]` and below `1`. -/
def IsBandSeq (θ : ℕ → ℝ) : Prop :=
  ∀ k, CellFamily.mesh (k + 1) < θ k ∧ θ k ≤ CellFamily.mesh k ∧ θ k < 1

theorem IsBandSeq.pos {θ : ℕ → ℝ} (hθ : IsBandSeq θ) (k : ℕ) : 0 < θ k :=
  (mesh_pos (k + 1)).trans (hθ k).1

/-- `2⁻ᵏ ≤ 2 θₖ`. -/
theorem IsBandSeq.mesh_le_two_mul {θ : ℕ → ℝ} (hθ : IsBandSeq θ) (k : ℕ) : CellFamily.mesh k ≤ 2 * θ k := by
  have h := (hθ k).1
  rw [mesh_succ] at h
  linarith

/-- Every `ε ∈ (0, 1)` lies in a dyadic band: `2⁻ᵏ⁻¹ < ε ≤ 2⁻ᵏ`. -/
theorem exists_band {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∃ k : ℕ, CellFamily.mesh (k + 1) < ε ∧ ε ≤ CellFamily.mesh k := by
  classical
  have hex : ∃ k : ℕ, CellFamily.mesh k < ε := (tendsto_mesh.eventually (gt_mem_nhds h0)).exists
  have hk₀ : CellFamily.mesh (Nat.find hex) < ε := Nat.find_spec hex
  have hk₀ne : Nat.find hex ≠ 0 := by
    intro h
    rw [h, mesh_zero] at hk₀
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk₀ne
  rw [hk] at hk₀
  refine ⟨k, hk₀, ?_⟩
  have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
  exact not_lt.mp hmin

/-- A mesh of band `k` below `2⁻ᴷ` has `K ≤ k`. -/
theorem le_of_band_of_lt_mesh {ε : ℝ} {k K : ℕ} (hk : CellFamily.mesh (k + 1) < ε) (hK : ε < CellFamily.mesh K) :
    K ≤ k := by
  by_contra h
  have : CellFamily.mesh K ≤ CellFamily.mesh (k + 1) := mesh_antitone (by omega)
  linarith

/-! ### The diagonal argument -/

/-- **From every band sequence to every real mesh.** `Good ε n C` is a countable family of estimates at mesh `ε`
(index `n`, constant `C`), weaker for larger `n` and larger `C` (`hn`, `hC`, for `ε ∈ (0, 1)`), and trivially true
on `[δ, 1)` for a large enough constant (`hbig`, e.g. a probability bound `≤ 1`). If along every band sequence some
`Good · n C` holds at every index, then some `Good · n C` holds at every `ε ∈ (0, 1)`. -/
theorem uniform_of_bandSeq (Good : ℝ → ℕ → ℝ → Prop)
    (hn : ∀ ε n n' C, 0 < ε → ε < 1 → n ≤ n' → Good ε n C → Good ε n' C)
    (hC : ∀ ε n C C', 0 < ε → ε < 1 → C ≤ C' → Good ε n C → Good ε n C')
    (hbig : ∀ (n : ℕ) (δ : ℝ), 0 < δ → ∃ C, ∀ ε, δ ≤ ε → ε < 1 → Good ε n C)
    (h : ∀ θ, IsBandSeq θ → ∃ n C, ∀ k, Good (θ k) n C) :
    ∃ n C, ∀ ε, 0 < ε → ε < 1 → Good ε n C := by
  classical
  by_contra hcon
  push Not at hcon
  -- for every `m` and every `K`: a failure of `Good · m m` in some band `k ≥ K`
  have key : ∀ m K : ℕ, ∃ k : ℕ, K ≤ k ∧ ∃ ε : ℝ, CellFamily.mesh (k + 1) < ε ∧ ε ≤ CellFamily.mesh k ∧
      ε < 1 ∧ ¬ Good ε m m := by
    intro m K
    obtain ⟨C₀, hC₀⟩ := hbig m (CellFamily.mesh K) (mesh_pos K)
    obtain ⟨ε, h0, h1, hng⟩ := hcon m (max (m : ℝ) C₀)
    have hlt : ε < CellFamily.mesh K := by
      by_contra hge
      push Not at hge
      exact hng (hC ε m C₀ _ h0 h1 (le_max_right _ _) (hC₀ ε hge h1))
    obtain ⟨k, hk1, hk2⟩ := exists_band h0 h1
    exact ⟨k, le_of_band_of_lt_mesh hk1 hlt, ε, hk1, hk2, h1,
      fun hg => hng (hC ε m m _ h0 h1 (le_max_left _ _) hg)⟩
  choose kk hkK εε hε1 hε2 hε3 hεng using key
  -- stage `m` uses the lower bound `Kst m` on the band index; the band indices increase strictly
  let idx : ℕ → ℕ := fun m => Nat.rec (kk 0 0) (fun m prev => kk (m + 1) (prev + 1)) m
  let Kst : ℕ → ℕ := fun m => Nat.casesOn m 0 (fun m' => idx m' + 1)
  have hidx : ∀ m, idx m = kk m (Kst m) := by
    intro m
    cases m with
    | zero => rfl
    | succ m => rfl
  have hstep : ∀ m, idx m < idx (m + 1) := by
    intro m
    have h := hkK (m + 1) (Kst (m + 1))
    rw [← hidx] at h
    exact Nat.lt_of_succ_le h
  have hmono : StrictMono idx := strictMono_nat_of_lt_succ hstep
  -- the band sequence
  let hdec : ∀ k, Decidable (∃ m, idx m = k) := fun _ => Classical.propDecidable _
  let θ : ℕ → ℝ := fun k =>
    if hk : ∃ m, idx m = k then εε (Classical.choose hk) (Kst (Classical.choose hk))
    else 3 / 4 * CellFamily.mesh k
  have hθ : IsBandSeq θ := by
    intro k
    by_cases hk : ∃ m, idx m = k
    · have hm := Classical.choose_spec hk
      simp only [θ, hk, ↓reduceDIte]
      have e : kk (Classical.choose hk) (Kst (Classical.choose hk)) = k := by rw [← hidx]; exact hm
      refine ⟨?_, ?_, hε3 _ _⟩
      · have := hε1 (Classical.choose hk) (Kst (Classical.choose hk)); rwa [e] at this
      · have := hε2 (Classical.choose hk) (Kst (Classical.choose hk)); rwa [e] at this
    · simp only [θ, hk, ↓reduceDIte]
      have h0 := mesh_pos k
      have h1 := mesh_le_one k
      refine ⟨?_, by linarith, by linarith⟩
      rw [mesh_succ]
      linarith
  have hθidx : ∀ m, θ (idx m) = εε m (Kst m) := by
    intro m
    have hk : ∃ m', idx m' = idx m := ⟨m, rfl⟩
    have hfind : Classical.choose hk = m := hmono.injective (Classical.choose_spec hk)
    simp only [θ, hk, ↓reduceDIte, hfind]
  obtain ⟨n, C, hgood⟩ := h θ hθ
  let m := max n ⌈C⌉₊
  have hgm := hgood (idx m)
  rw [hθidx m] at hgm
  have hpos : 0 < εε m (Kst m) := (mesh_pos _).trans (hε1 m (Kst m))
  have h1 : εε m (Kst m) < 1 := hε3 m (Kst m)
  have hg1 := hn _ n m C hpos h1 (le_max_left _ _) hgm
  have hCm : C ≤ (m : ℝ) :=
    (Nat.le_ceil C).trans (by exact_mod_cast le_max_right n ⌈C⌉₊)
  exact hεng m (Kst m) (hC _ m C m hpos h1 hCm hg1)

/-- The exponents `1/(n+1)` of the countable family. -/
theorem exists_inv_succ_le {a : ℝ} (ha : 0 < a) : ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ a := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
  exact ⟨n, hn.le⟩

theorem inv_succ_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity

theorem inv_succ_anti {n n' : ℕ} (h : n ≤ n') : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

/-- **The bad-event instance.** `b ε β p` is an outer probability (`≤ 1`), smaller for smaller `(β, p)` at each
`ε ∈ (0, 1)`. If along every band sequence `b (θ k) β p ≤ C θₖ^α` for some `α, β, p > 0` and `C`, then the same
holds at every real `ε ∈ (0, 1)` with constants independent of `ε`. -/
theorem uniform_rate_of_bandSeq (b : ℝ → ℝ → ℝ → ℝ≥0∞) (hb1 : ∀ ε β p, b ε β p ≤ 1)
    (hmono : ∀ ε β p β' p', 0 < ε → ε < 1 → β' ≤ β → p' ≤ p → b ε β' p' ≤ b ε β p)
    (h : ∀ θ, IsBandSeq θ → ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ k, b (θ k) β p ≤ ENNReal.ofReal (C * θ k ^ α)) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → b ε β p ≤ ENNReal.ofReal (C * ε ^ α) := by
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let Good : ℝ → ℕ → ℝ → Prop := fun ε n C => b ε (τ n) (τ n) ≤ ENNReal.ofReal (C * ε ^ τ n)
  have hn : ∀ ε n n' C, 0 < ε → ε < 1 → n ≤ n' → Good ε n C → Good ε n' C := by
    intro ε n n' C h0 h1 hnn' hg
    have hτ : τ n' ≤ τ n := inv_succ_anti hnn'
    have hpow : ε ^ τ n ≤ ε ^ τ n' := Real.rpow_le_rpow_of_exponent_ge h0 h1.le hτ
    refine (hmono ε (τ n) (τ n) (τ n') (τ n') h0 h1 hτ hτ).trans (hg.trans ?_)
    rcases le_total C 0 with hC0 | hC0
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hC0 (Real.rpow_nonneg h0.le _))]
      exact zero_le
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hC0)
  have hC : ∀ ε n C C', 0 < ε → ε < 1 → C ≤ C' → Good ε n C → Good ε n C' := by
    intro ε n C C' h0 _ hCC' hg
    exact hg.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg h0.le _)))
  have hbig : ∀ (n : ℕ) (δ : ℝ), 0 < δ → ∃ C, ∀ ε, δ ≤ ε → ε < 1 → Good ε n C := by
    intro n δ hδ
    refine ⟨(δ ^ τ n)⁻¹, fun ε hδε _ => (hb1 _ _ _).trans ?_⟩
    have hδpos : 0 < δ ^ τ n := Real.rpow_pos_of_pos hδ _
    have hle : δ ^ τ n ≤ ε ^ τ n := Real.rpow_le_rpow hδ.le hδε (inv_succ_pos n).le
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_mul_eq_div, le_div_iff₀ hδpos, one_mul]
    exact hle
  have hθ : ∀ θ, IsBandSeq θ → ∃ n C, ∀ k, Good (θ k) n C := by
    intro θ hθ
    obtain ⟨α, hα, β, hβ, p, hp, C, hbound⟩ := h θ hθ
    obtain ⟨n, hn'⟩ := exists_inv_succ_le (lt_min hα (lt_min hβ hp))
    refine ⟨n, max C 0, fun k => ?_⟩
    have h0 := hθ.pos k
    have h1 := (hθ k).2.2
    have hτα : τ n ≤ α := hn'.trans (min_le_left _ _)
    have hτβ : τ n ≤ β := hn'.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hτp : τ n ≤ p := hn'.trans ((min_le_right _ _).trans (min_le_right _ _))
    refine (hmono (θ k) β p (τ n) (τ n) h0 h1 hτβ hτp).trans ((hbound k).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hpow : θ k ^ α ≤ θ k ^ τ n := Real.rpow_le_rpow_of_exponent_ge h0 h1.le hτα
    calc C * θ k ^ α ≤ max C 0 * θ k ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h0.le _)
      _ ≤ max C 0 * θ k ^ τ n := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  obtain ⟨n, C, hall⟩ := uniform_of_bandSeq Good hn hC hbig hθ
  exact ⟨τ n, inv_succ_pos n, τ n, inv_succ_pos n, τ n, inv_succ_pos n, C, hall⟩

end MatedCRTHarmonic.GMSMain.EpsB
