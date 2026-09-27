import LatticeProb.Prob.AkcogluKrengelAE.UnitScaleLowerBound

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Coarse-graining (Step 4, part E)

Blowing up a box by the factor `m` (every site `z` becomes the cube `m z + [0, m) ^ d`) turns box
splits into box splits, translates into translates, and the cube of side `k` into the cube of side
`k m`. The coarse-grained process `coarse f m` then inherits all of `f`'s hypotheses for the
sublattice action `z ↦ τ (m • z)`, with `cubeRatio (coarse f m) k = cubeRatio f (k m)`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Blowing up a box by the factor `m` gives the box scaled by `m`, with upper corner shifted by `m
- 1`. -/
theorem blowup_latticeBox_eq_latticeBox_smul {d m : ℕ} (hm : 1 ≤ m) (a b : Site d) :
    blowup m (latticeBox a b) =
      latticeBox ((m : ℤ) • a) ((m : ℤ) • b + fun _ => (m : ℤ) - 1) := by
  have hm0 : (0 : ℤ) < (m : ℤ) := (by exact_mod_cast hm)
  have hmne : (m : ℤ) ≠ 0 := ne_of_gt hm0
  have hsm : ∀ (v : Site d) (i : Fin d), ((m : ℤ) • v) i = (m : ℤ) * v i :=
    fun v i => by simp []
  have hadd : ∀ (v : Site d) (i : Fin d),
      ((m : ℤ) • v + fun _ : Fin d => (m : ℤ) - 1) i = (m : ℤ) * v i + ((m : ℤ) - 1) :=
    fun v i => by simp [zsmul_eq_mul]
  ext y
  rw [mem_latticeBox_iff]
  constructor
  · intro hy
    rw [blowup, Finset.mem_biUnion] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rw [map_addRight_latticeCube_eq_latticeBox d m ((m : ℤ) • z), mem_latticeBox_iff] at hyz
    intro i
    have h1 := (mem_latticeBox_iff a b z).1 hz i
    have h2 := hyz i
    rw [hsm z i] at h2
    rw [hsm a i, hadd b i]
    exact ⟨le_trans (mul_le_mul_of_nonneg_left h1.1 hm0.le) h2.1,
      by linarith [mul_le_mul_of_nonneg_left h1.2 hm0.le, h2.2]⟩
  · intro hy
    rw [blowup, Finset.mem_biUnion]
    refine ⟨fun i => y i / (m : ℤ), ?_, ?_⟩
    · rw [mem_latticeBox_iff]
      intro i
      have h := hy i
      rw [hsm a i, hadd b i] at h
      exact ⟨(Int.le_ediv_iff_mul_le hm0).2 (by linarith [h.1]),
        (Int.ediv_le_iff_le_mul hm0).2 (by linarith [h.2])⟩
    · rw [map_addRight_latticeCube_eq_latticeBox d m ((m : ℤ) • fun i => y i / (m : ℤ)),
        mem_latticeBox_iff]
      intro i
      have h := hy i
      rw [hsm a i, hadd b i] at h
      rw [hsm (fun i => y i / (m : ℤ)) i]
      have hdiv := Int.emod_add_mul_ediv (y i) (m : ℤ)
      have hmod_nn := Int.emod_nonneg (y i) hmne
      have hmod_lt := Int.emod_lt_of_pos (y i) hm0
      refine ⟨?_, ?_⟩ <;> linarith


/-- The size-`m` blocks of two distinct sites under blow-up are disjoint. -/
theorem disjoint_map_addRight_cube_smul_of_ne {d m : ℕ} (_unused_hm : 1 ≤ m) {z w : Site d}
    (hzw : z ≠ w) :
    Disjoint ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding)
      ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • w)).toEmbedding) := by
  rw [map_addRight_latticeCube_eq_latticeBox, map_addRight_latticeCube_eq_latticeBox]
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  have h1 := (mem_latticeBox_iff _ _ y).1 hy1
  have h2 := (mem_latticeBox_iff _ _ y).1 hy2
  obtain ⟨i, hi⟩ : ∃ i : Fin d, z i ≠ w i := by
    by_contra h
    push Not at h
    exact hzw (funext fun i => h i)
  have e1 := h1 i
  have e2 := h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
  have hbound : |(m : ℤ) * (z i - w i)| ≤ (m : ℤ) - 1 := by
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hge : (m : ℤ) ≤ |(m : ℤ) * (z i - w i)| := by
    rw [abs_mul]
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
    have ht : (1 : ℤ) ≤ |z i - w i| := by
      have hpos : (0 : ℤ) < |z i - w i| := abs_pos.mpr (sub_ne_zero.mpr hi)
      omega
    rw [abs_of_nonneg hm0]
    calc (m : ℤ) = (m : ℤ) * 1 := by ring
      _ ≤ (m : ℤ) * |z i - w i| := mul_le_mul_of_nonneg_left ht hm0
  omega

/-- Blow-up commutes with union, and with disjointness of two finsets. -/
theorem blowup_union_and_disjoint {d m : ℕ} (hm : 1 ≤ m) (B₁ B₂ : Finset (Site d)) :
    blowup m (B₁ ∪ B₂) = blowup m B₁ ∪ blowup m B₂ ∧
      (Disjoint B₁ B₂ → Disjoint (blowup m B₁) (blowup m B₂)) := by
  constructor
  · unfold blowup
    exact Finset.union_biUnion
  · intro h
    unfold blowup
    rw [Finset.disjoint_biUnion_left]
    intro z hz
    rw [Finset.disjoint_biUnion_right]
    intro w hw
    exact disjoint_map_addRight_cube_smul_of_ne hm (fun hzw => (Finset.disjoint_left.mp h hz)
        (hzw.symm ▸ hw))


/-- Blow-up by `m` turns an `IsBoxSplit` into an `IsBoxSplit` of the blown-up pieces. -/
theorem isBoxSplit_blowup {d m : ℕ} (hm : 1 ≤ m) {B B₁ B₂ : Finset (Site d)}
    (h : IsBoxSplit B B₁ B₂) : IsBoxSplit (blowup m B) (blowup m B₁) (blowup m B₂) := by
  obtain ⟨⟨a, b, rfl⟩, ⟨a₁, b₁, rfl⟩, ⟨a₂, b₂, rfl⟩, hdisj, hun⟩ := h
  refine ⟨⟨_, _, blowup_latticeBox_eq_latticeBox_smul hm a b⟩, ⟨_, _,
      blowup_latticeBox_eq_latticeBox_smul hm a₁ b₁⟩,
    ⟨_, _, blowup_latticeBox_eq_latticeBox_smul hm a₂ b₂⟩, (blowup_union_and_disjoint hm _ _).2
        hdisj, ?_⟩
  rw [← (blowup_union_and_disjoint hm _ _).1, hun]

/-- Blow-up commutes with translation, scaling the translation vector by `m`. -/
theorem blowup_map_addRight_eq_map_addRight_blowup {d : ℕ} (m : ℕ) (B : Finset (Site d)) (z
    : Site d) :
    blowup m (B.map (Equiv.addRight z).toEmbedding) =
      (blowup m B).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding := by
  ext y
  simp only [blowup, Finset.mem_biUnion, Finset.mem_map, Equiv.coe_toEmbedding,
    Equiv.coe_addRight]
  constructor
  · rintro ⟨w, ⟨b, hb, rfl⟩, v, hv, rfl⟩
    refine ⟨v + (m : ℤ) • b, ⟨b, hb, v, hv, rfl⟩, ?_⟩
    rw [add_assoc, ← smul_add]
  · rintro ⟨t, ⟨b, hb, v, hv, rfl⟩, ht⟩
    refine ⟨b + z, ⟨b, hb, rfl⟩, v, hv, ?_⟩
    rw [← ht, smul_add, add_assoc]


/-- The size-`m` blocks of two distinct sites under blow-up are disjoint. -/
theorem disjoint_map_addRight_cube_smul_of_ne' {d m : ℕ} (hm : 1 ≤ m) {z w : Site d} (hne :
    z ≠ w) :
    Disjoint ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding)
      ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • w)).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  obtain ⟨v1, hv1, h1⟩ := Finset.mem_map.1 hy1
  obtain ⟨v2, hv2, h2⟩ := Finset.mem_map.1 hy2
  refine hne (funext fun i => ?_)
  have hmz : (0 : ℤ) < (m : ℤ) := by omega
  have b1 := ((mem_latticeBox_iff (0 : Site d) (fun _ => (m : ℤ) - 1) v1).1 hv1 i)
  have b2 := ((mem_latticeBox_iff (0 : Site d) (fun _ => (m : ℤ) - 1) v2).1 hv2 i)
  simp only [Pi.zero_apply] at b1 b2
  have e1 : v1 i + (m : ℤ) * z i = y i := by
    have hh := congrFun h1 i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have e2 : v2 i + (m : ℤ) * w i = y i := by
    have hh := congrFun h2 i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have hmul : (m : ℤ) * (z i - w i) = v2 i - v1 i := by linarith
  have key : (m : ℤ) * |z i - w i| < (m : ℤ) * 1 := by
    calc (m : ℤ) * |z i - w i| = |(m : ℤ) * (z i - w i)| := by rw [abs_mul, abs_of_pos hmz]
      _ = |v2 i - v1 i| := by rw [hmul]
      _ ≤ (m : ℤ) - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      _ < (m : ℤ) * 1 := by omega
  have hlt : |z i - w i| < 1 := lt_of_mul_lt_mul_left key (le_of_lt hmz)
  have ha := (abs_lt.mp hlt).1
  have hb := (abs_lt.mp hlt).2
  omega

/-- `blowup m B` has `m ^ d * B.card` sites. -/
theorem card_blowup_eq_pow_mul_card {d m : ℕ} (hm : 1 ≤ m) (B : Finset (Site d)) :
    (blowup m B).card = m ^ d * B.card := by
  rw [blowup, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun z _ => by rw [Finset.card_map, card_latticeCube_eq_pow]),
      Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_comm _ _
  · intro z _ w _ hne
    exact disjoint_map_addRight_cube_smul_of_ne' hm hne


/-- Blowing up the cube of side `k` by `m` gives the cube of side `k * m`. -/
theorem blowup_cube_eq_cube_mul {d m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    blowup m (latticeCube d k) = latticeCube d (k * m) := by
  have h := blowup_latticeBox_eq_latticeBox_smul (d := d) hm (0 : Site d) (fun _ : Fin d => (k : ℤ)
      - 1)
  rw [show latticeCube d k = latticeBox (0 : Site d) (fun _ : Fin d => (k : ℤ) - 1) from rfl, h]
  unfold latticeBox latticeCube
  congr 1
  all_goals (funext i; simp only [Pi.add_apply, Pi.smul_apply]; push_cast; ring)


/-- The coarse-grained process `coarse f m` is measurable, satisfies the volume bound with the same
`C`, is subadditive along two-box splits, and is stationary under the sublattice action `z ↦ τ
(m • z)`. -/
theorem coarse_isBoxSplit_and_stat {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (τ : Site d
    → Ω → Ω)
    (hmeas : ∀ A, Measurable (f A)) (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω)) {m : ℕ} (hm : 1 ≤ m) :
    (∀ A, Measurable (coarse f m A)) ∧
      (∀ A ω, 0 ≤ coarse f m A ω ∧ coarse f m A ω ≤ C * A.card) ∧
      (∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → coarse f m B ω ≤ coarse f m B₁ ω + coarse f m B₂ ω) ∧
      ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
        coarse f m (A.map (Equiv.addRight z).toEmbedding) ω = coarse f m A (τ ((m : ℤ) • z) ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    rw [show coarse f m A = fun ω => f (blowup m A) ω / (m : ℝ) ^ d from rfl]
    exact (hmeas (blowup m A)).div_const _
  · intro A ω
    rw [show coarse f m A ω = f (blowup m A) ω / (m : ℝ) ^ d from rfl]
    refine ⟨div_nonneg (hC (blowup m A) ω).1 (by positivity), ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ d)]
    have h := (hC (blowup m A) ω).2
    rw [card_blowup_eq_pow_mul_card hm A] at h
    push_cast at h
    nlinarith [h]
  · intro B B₁ B₂ ω hs
    rw [show coarse f m B ω = f (blowup m B) ω / (m : ℝ) ^ d from rfl,
      show coarse f m B₁ ω = f (blowup m B₁) ω / (m : ℝ) ^ d from rfl,
      show coarse f m B₂ ω = f (blowup m B₂) ω / (m : ℝ) ^ d from rfl]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hsub _ _ _ ω (isBoxSplit_blowup hm hs)) (by positivity)
  · intro A z ω
    rw [show coarse f m (A.map (Equiv.addRight z).toEmbedding) ω =
        f (blowup m (A.map (Equiv.addRight z).toEmbedding)) ω / (m : ℝ) ^ d from rfl,
      show coarse f m A (τ ((m : ℤ) • z) ω) =
        f (blowup m A) (τ ((m : ℤ) • z) ω) / (m : ℝ) ^ d from rfl]
    rw [blowup_map_addRight_eq_map_addRight_blowup m A z, hstat]


omit [MeasurableSpace Ω] in
/-- `cubeRatio (coarse f m) k` equals `cubeRatio f (k * m)`. -/
theorem cubeRatio_coarse_eq_cubeRatio_mul {d : ℕ} (f : Finset (Site d) → Ω → ℝ) {m : ℕ} (hm
    : 1 ≤ m) (k : ℕ)
    (ω : Ω) : cubeRatio (coarse f m) k ω = cubeRatio f (k * m) ω := by
  unfold cubeRatio coarse
  rw [blowup_cube_eq_cube_mul hm, Nat.cast_mul, mul_pow, div_div, mul_comm ((m : ℝ) ^ d)]

end LatticeProb
