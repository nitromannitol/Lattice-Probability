/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G2

/-!
# DZZ Lemma 3.13, cell geometry III: the door, vertical contact (P2-DZZ313G)

DZZ arXiv:1807.00422 l. 1327–1331 (`Λ_j`, its middle `x_j`, the boxes of `𝒞_j` at `x_j`): the case where
`𝖢` lies to the left of `𝖢'`. Own elementary proof of the coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

set_option maxHeartbeats 1000000 in
lemma door_vert {C C' : DyBox} (hC : IsCell m δ C) (hC' : IsCell m δ C') {k : ℕ} (hk : 1 ≤ k)
    (hr : SideRatio ((2 : ℝ)⁻¹ ^ k) C C')
    (ha : ((C.j : ℝ) + 1) * C.side = C'.j * C'.side)
    (h1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side)
    (h2 : (C'.k : ℝ) * C'.side < (C.k + 1) * C.side) :
    ∃ x s s', L313DoorSide m δ k C x s ∧ L313DoorSide m δ k C' x s' ∧ Neighbour s s' := by
  obtain ⟨L1, L2⟩ := levels_of_sideRatio hr
  obtain ⟨κ, c1, c2, c3, c4⟩ := exists_contact (n := C.n) (n' := C'.n) h1 h2
  have hsd : C.side = (2 : ℝ)⁻¹ ^ C.n := rfl
  have hsd' : C'.side = (2 : ℝ)⁻¹ ^ C'.n := rfl
  rw [← hsd] at c1 c2
  rw [← hsd'] at c3 c4
  set L := max C.n C'.n with hL
  set ε : ℝ := (2 : ℝ)⁻¹ ^ k with hεdef
  set ℓ : ℝ := (2 : ℝ)⁻¹ ^ L with hℓdef
  set w : ℝ := (2 : ℝ)⁻¹ ^ (C.n + 2 * k) with hwdef
  set w' : ℝ := (2 : ℝ)⁻¹ ^ (C'.n + 2 * k) with hw'def
  have hs := side_pos' C
  have hs' := side_pos' C'
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hℓ0 : 0 < ℓ := by positivity
  have hw0 : 0 < w := by positivity
  have hw0' : 0 < w' := by positivity
  have hℓs : ℓ ≤ C.side := ipow_le (le_max_left _ _)
  have hℓs' : ℓ ≤ C'.side := ipow_le (le_max_right _ _)
  have hεs : ε * C.side ≤ ℓ := by rw [hsd, ← pow_add]; exact ipow_le (by omega)
  have hεs' : ε * C'.side ≤ ℓ := by rw [hsd', ← pow_add]; exact ipow_le (by omega)
  have hℓ2 : ℓ / 2 = (2 : ℝ)⁻¹ ^ (L + 1) := by rw [hℓdef, pow_succ]; ring
  have hwℓ : w ≤ ℓ / 2 := by rw [hℓ2]; exact ipow_le (by omega)
  have hwℓ' : w' ≤ ℓ / 2 := by rw [hℓ2]; exact ipow_le (by omega)
  have hr1 : ε * C.side ≤ C'.side := hr.1
  have hr2 : ε * C'.side ≤ C.side := by
    have := hr.2; rwa [le_div_iff₀ hε0, mul_comm] at this
  have hεss : ε * C.side ≤ C.side := mul_le_of_le_one_left hs.le hε1
  have hεss' : ε * C'.side ≤ C'.side := mul_le_of_le_one_left hs'.le hε1
  have hj0 : (0 : ℝ) ≤ C.j * C.side := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hk0 : (0 : ℝ) ≤ C.k * C.side := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hk0' : (0 : ℝ) ≤ C'.k * C'.side := mul_nonneg (Nat.cast_nonneg _) hs'.le
  have hJ1 := succ_j_side_le_one C'
  have hK1 := succ_k_side_le_one C
  have hK1' := succ_k_side_le_one C'
  set A : ℝ := ((C.j : ℝ) + 1) * C.side with hA
  -- grid representations
  have eY : (κ + 1 / 2 : ℝ) * ℓ = (2 * κ + 1) * (2 : ℝ)⁻¹ ^ (L + 1) := by
    rw [← hℓ2]; ring
  have sp1 := ipow_split (show L + 1 ≤ C.n + 2 * k by omega)
  have sp2 := ipow_split (show L + 1 ≤ C'.n + 2 * k by omega)
  have sp3 := ipow_split (Nat.le_add_right C.n (2 * k))
  have sp4 := ipow_split (Nat.le_add_right C'.n (2 * k))
  rw [Nat.add_sub_cancel_left] at sp3 sp4
  have hi1 : 1 ≤ (C.j + 1) * 2 ^ (2 * k) := Nat.mul_pos (Nat.succ_pos _) (by positivity)
  have ei : (((C.j + 1) * 2 ^ (2 * k) - 1 : ℕ) : ℝ) = ((C.j : ℝ) + 1) * 2 ^ (2 * k) - 1 := by
    rw [Nat.cast_sub hi1]; push_cast; ring
  obtain ⟨x, hxr, hxi⟩ : ∃ x : ℂ, x.re = A ∧ x.im = (κ + 1 / 2) * ℓ := ⟨⟨_, _⟩, rfl, rfl⟩
  obtain ⟨p, hpr, hpi⟩ : ∃ p : ℂ, p.re = A - w / 2 ∧ p.im = (κ + 1 / 2) * ℓ + w / 2 :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  obtain ⟨p', hpr', hpi'⟩ : ∃ p : ℂ, p.re = A + w' / 2 ∧ p.im = (κ + 1 / 2) * ℓ + w' / 2 :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  have gpr : p.re = ((((C.j + 1) * 2 ^ (2 * k) - 1 : ℕ) : ℝ) + 1 / 2) * w := by
    rw [hpr, ei, hA, hsd, sp3]; ring
  have gpi : p.im = ((((2 * κ + 1) * 2 ^ (C.n + 2 * k - (L + 1)) : ℕ) : ℝ) + 1 / 2) * w := by
    rw [hpi, eY, sp1]; push_cast; ring
  have gpr' : p'.re = (((C'.j * 2 ^ (2 * k) : ℕ) : ℝ) + 1 / 2) * w' := by
    rw [hpr', ha, hsd', sp4]; push_cast; ring
  have gpi' : p'.im = ((((2 * κ + 1) * 2 ^ (C'.n + 2 * k - (L + 1)) : ℕ) : ℝ) + 1 / 2) * w' := by
    rw [hpi', eY, sp2]; push_cast; ring
  have hp1 : p.re ≤ 1 := by rw [hpr]; linarith
  have hp2 : p.im ≤ 1 := by rw [hpi]; linarith
  have hp1' : p'.re ≤ 1 := by rw [hpr']; linarith
  have hp2' : p'.im ≤ 1 := by rw [hpi']; linarith
  have hpV : p ∈ dzzV := ⟨by rw [hpr]; linarith, hp1, by rw [hpi]; linarith, hp2⟩
  have hpV' : p' ∈ dzzV := ⟨by rw [hpr']; linarith, hp1', by rw [hpi']; linarith, hp2'⟩
  have hCp : C.Mem p := ⟨hpV, boxAt_eq_of_ho (by rw [hpr]; linarith) (by rw [hpr]; linarith)
    (by rw [hpi]; linarith) (by rw [hpi]; linarith)⟩
  have hCp' : C'.Mem p' := ⟨hpV', boxAt_eq_of_ho (by rw [hpr']; linarith) (by rw [hpr']; linarith)
    (by rw [hpi']; linarith) (by rw [hpi']; linarith)⟩
  have mem1 := fun q => mem_boxAt_of_center (q := q) hp1 hp2 gpr gpi
  have mem2 := fun q => mem_boxAt_of_center (q := q) hp1' hp2' gpr' gpi'
  have hxs : x ∈ (boxAt (C.n + 2 * k) p).closedBox := mem1 x
    (by rw [hxr, hpr, abs_le]; constructor <;> linarith)
    (by rw [hxi, hpi, abs_le]; constructor <;> linarith)
  have hxs' : x ∈ (boxAt (C'.n + 2 * k) p').closedBox := mem2 x
    (by rw [hxr, hpr', abs_le]; constructor <;> linarith)
    (by rw [hxi, hpi', abs_le]; constructor <;> linarith)
  refine ⟨x, boxAt (C.n + 2 * k) p, boxAt (C'.n + 2 * k) p',
    ⟨rfl, boxAt_sub_cell hCp (by omega), hxs, ⟨?_, Or.inr ⟨⟨?_, ?_⟩, Or.inl ?_⟩⟩, ?_⟩,
    ⟨rfl, boxAt_sub_cell hCp' (by omega), hxs', ⟨?_, Or.inr ⟨⟨?_, ?_⟩, Or.inr ?_⟩⟩, ?_⟩, ?_⟩
  all_goals try simp only [← hεdef]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hxr]; linarith
    · rw [hxr]
    · rw [hxi]; linarith
    · rw [hxi]; linarith
  · rw [hxi]; linarith
  · rw [hxi]; linarith
  · rw [hxr]; linarith
  · rintro z hz ⟨d1, d2⟩
    rw [hxr, abs_lt] at d1
    rw [hxi, abs_lt] at d2
    by_cases hzA : z.re < A
    · rw [cellSide_eq_of_ho hC hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hεss
    · rw [cellSide_eq_of_ho hC' hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hr1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hxr]; linarith
    · rw [hxr]; linarith
    · rw [hxi]; linarith
    · rw [hxi]; linarith
  · rw [hxi]; linarith
  · rw [hxi]; linarith
  · rw [hxr]; linarith
  · rintro z hz ⟨d1, d2⟩
    rw [hxr, abs_lt] at d1
    rw [hxi, abs_lt] at d2
    by_cases hzA : z.re < A
    · rw [cellSide_eq_of_ho hC hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hr2
    · rw [cellSide_eq_of_ho hC' hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hεss'
  · have hsc := center_boxAt_of_center hp1 hp2 gpr gpi
    have hsc' := center_boxAt_of_center hp1' hp2' gpr' gpi'
    refine ⟨fun e => ?_, fun hsub => ?_⟩
    · have e2 := congrArg (fun b => (DyBox.center b).re) e
      simp only [hsc, hsc', hpr, hpr'] at e2
      linarith
    · obtain ⟨q, hqr, hqi⟩ : ∃ q : ℂ, q.re = A ∧ q.im = (κ + 1 / 2) * ℓ + min w w' :=
        ⟨⟨_, _⟩, rfl, rfl⟩
      have hμ0 : 0 < min w w' := lt_min hw0 hw0'
      have hμ1 := min_le_left w w'
      have hμ2 := min_le_right w w'
      have hq1 : q ∈ (boxAt (C.n + 2 * k) p).closedBox := mem1 q
        (by rw [hqr, hpr, abs_le]; constructor <;> linarith)
        (by rw [hqi, hpi, abs_le]; constructor <;> linarith)
      have hq2 : q ∈ (boxAt (C'.n + 2 * k) p').closedBox := mem2 q
        (by rw [hqr, hpr', abs_le]; constructor <;> linarith)
        (by rw [hqi, hpi', abs_le]; constructor <;> linarith)
      have e := hsub ⟨hxs, hxs'⟩ ⟨hq1, hq2⟩
      have e2 := congrArg Complex.im e
      rw [hxi, hqi] at e2
      linarith

set_option maxHeartbeats 1000000 in
lemma door_horiz {C C' : DyBox} (hC : IsCell m δ C) (hC' : IsCell m δ C') {k : ℕ} (hk : 1 ≤ k)
    (hr : SideRatio ((2 : ℝ)⁻¹ ^ k) C C')
    (ha : ((C.k : ℝ) + 1) * C.side = C'.k * C'.side)
    (h1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side)
    (h2 : (C'.j : ℝ) * C'.side < (C.j + 1) * C.side) :
    ∃ x s s', L313DoorSide m δ k C x s ∧ L313DoorSide m δ k C' x s' ∧ Neighbour s s' := by
  obtain ⟨L1, L2⟩ := levels_of_sideRatio hr
  obtain ⟨κ, c1, c2, c3, c4⟩ := exists_contact (n := C.n) (n' := C'.n) h1 h2
  have hsd : C.side = (2 : ℝ)⁻¹ ^ C.n := rfl
  have hsd' : C'.side = (2 : ℝ)⁻¹ ^ C'.n := rfl
  rw [← hsd] at c1 c2
  rw [← hsd'] at c3 c4
  set L := max C.n C'.n with hL
  set ε : ℝ := (2 : ℝ)⁻¹ ^ k with hεdef
  set ℓ : ℝ := (2 : ℝ)⁻¹ ^ L with hℓdef
  set w : ℝ := (2 : ℝ)⁻¹ ^ (C.n + 2 * k) with hwdef
  set w' : ℝ := (2 : ℝ)⁻¹ ^ (C'.n + 2 * k) with hw'def
  have hs := side_pos' C
  have hs' := side_pos' C'
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hℓ0 : 0 < ℓ := by positivity
  have hw0 : 0 < w := by positivity
  have hw0' : 0 < w' := by positivity
  have hℓs : ℓ ≤ C.side := ipow_le (le_max_left _ _)
  have hℓs' : ℓ ≤ C'.side := ipow_le (le_max_right _ _)
  have hεs : ε * C.side ≤ ℓ := by rw [hsd, ← pow_add]; exact ipow_le (by omega)
  have hεs' : ε * C'.side ≤ ℓ := by rw [hsd', ← pow_add]; exact ipow_le (by omega)
  have hℓ2 : ℓ / 2 = (2 : ℝ)⁻¹ ^ (L + 1) := by rw [hℓdef, pow_succ]; ring
  have hwℓ : w ≤ ℓ / 2 := by rw [hℓ2]; exact ipow_le (by omega)
  have hwℓ' : w' ≤ ℓ / 2 := by rw [hℓ2]; exact ipow_le (by omega)
  have hr1 : ε * C.side ≤ C'.side := hr.1
  have hr2 : ε * C'.side ≤ C.side := by
    have := hr.2; rwa [le_div_iff₀ hε0, mul_comm] at this
  have hεss : ε * C.side ≤ C.side := mul_le_of_le_one_left hs.le hε1
  have hεss' : ε * C'.side ≤ C'.side := mul_le_of_le_one_left hs'.le hε1
  have hj0 : (0 : ℝ) ≤ C.k * C.side := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hk0 : (0 : ℝ) ≤ C.j * C.side := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hk0' : (0 : ℝ) ≤ C'.j * C'.side := mul_nonneg (Nat.cast_nonneg _) hs'.le
  have hJ1 := succ_k_side_le_one C'
  have hK1 := succ_j_side_le_one C
  have hK1' := succ_j_side_le_one C'
  set A : ℝ := ((C.k : ℝ) + 1) * C.side with hA
  -- grid representations
  have eY : (κ + 1 / 2 : ℝ) * ℓ = (2 * κ + 1) * (2 : ℝ)⁻¹ ^ (L + 1) := by
    rw [← hℓ2]; ring
  have sp1 := ipow_split (show L + 1 ≤ C.n + 2 * k by omega)
  have sp2 := ipow_split (show L + 1 ≤ C'.n + 2 * k by omega)
  have sp3 := ipow_split (Nat.le_add_right C.n (2 * k))
  have sp4 := ipow_split (Nat.le_add_right C'.n (2 * k))
  rw [Nat.add_sub_cancel_left] at sp3 sp4
  have hi1 : 1 ≤ (C.k + 1) * 2 ^ (2 * k) := Nat.mul_pos (Nat.succ_pos _) (by positivity)
  have ei : (((C.k + 1) * 2 ^ (2 * k) - 1 : ℕ) : ℝ) = ((C.k : ℝ) + 1) * 2 ^ (2 * k) - 1 := by
    rw [Nat.cast_sub hi1]; push_cast; ring
  obtain ⟨x, hxi, hxr⟩ : ∃ x : ℂ, x.im = A ∧ x.re = (κ + 1 / 2) * ℓ := ⟨⟨_, _⟩, rfl, rfl⟩
  obtain ⟨p, hpi, hpr⟩ : ∃ p : ℂ, p.im = A - w / 2 ∧ p.re = (κ + 1 / 2) * ℓ + w / 2 :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  obtain ⟨p', hpi', hpr'⟩ : ∃ p : ℂ, p.im = A + w' / 2 ∧ p.re = (κ + 1 / 2) * ℓ + w' / 2 :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  have gpi : p.im = ((((C.k + 1) * 2 ^ (2 * k) - 1 : ℕ) : ℝ) + 1 / 2) * w := by
    rw [hpi, ei, hA, hsd, sp3]; ring
  have gpr : p.re = ((((2 * κ + 1) * 2 ^ (C.n + 2 * k - (L + 1)) : ℕ) : ℝ) + 1 / 2) * w := by
    rw [hpr, eY, sp1]; push_cast; ring
  have gpi' : p'.im = (((C'.k * 2 ^ (2 * k) : ℕ) : ℝ) + 1 / 2) * w' := by
    rw [hpi', ha, hsd', sp4]; push_cast; ring
  have gpr' : p'.re = ((((2 * κ + 1) * 2 ^ (C'.n + 2 * k - (L + 1)) : ℕ) : ℝ) + 1 / 2) * w' := by
    rw [hpr', eY, sp2]; push_cast; ring
  have hp1 : p.re ≤ 1 := by rw [hpr]; linarith
  have hp2 : p.im ≤ 1 := by rw [hpi]; linarith
  have hp1' : p'.re ≤ 1 := by rw [hpr']; linarith
  have hp2' : p'.im ≤ 1 := by rw [hpi']; linarith
  have hpV : p ∈ dzzV := ⟨by rw [hpr]; linarith, hp1, by rw [hpi]; linarith, hp2⟩
  have hpV' : p' ∈ dzzV := ⟨by rw [hpr']; linarith, hp1', by rw [hpi']; linarith, hp2'⟩
  have hCp : C.Mem p := ⟨hpV, boxAt_eq_of_ho (by rw [hpr]; linarith) (by rw [hpr]; linarith)
    (by rw [hpi]; linarith) (by rw [hpi]; linarith)⟩
  have hCp' : C'.Mem p' := ⟨hpV', boxAt_eq_of_ho (by rw [hpr']; linarith) (by rw [hpr']; linarith)
    (by rw [hpi']; linarith) (by rw [hpi']; linarith)⟩
  have mem1 := fun q => mem_boxAt_of_center (q := q) hp1 hp2 gpr gpi
  have mem2 := fun q => mem_boxAt_of_center (q := q) hp1' hp2' gpr' gpi'
  have hxs : x ∈ (boxAt (C.n + 2 * k) p).closedBox := mem1 x
    (by rw [hxr, hpr, abs_le]; constructor <;> linarith)
    (by rw [hxi, hpi, abs_le]; constructor <;> linarith)
  have hxs' : x ∈ (boxAt (C'.n + 2 * k) p').closedBox := mem2 x
    (by rw [hxr, hpr', abs_le]; constructor <;> linarith)
    (by rw [hxi, hpi', abs_le]; constructor <;> linarith)
  refine ⟨x, boxAt (C.n + 2 * k) p, boxAt (C'.n + 2 * k) p',
    ⟨rfl, boxAt_sub_cell hCp (by omega), hxs, ⟨?_, Or.inl ⟨⟨?_, ?_⟩, Or.inl ?_⟩⟩, ?_⟩,
    ⟨rfl, boxAt_sub_cell hCp' (by omega), hxs', ⟨?_, Or.inl ⟨⟨?_, ?_⟩, Or.inr ?_⟩⟩, ?_⟩, ?_⟩
  all_goals try simp only [← hεdef]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hxr] <;> linarith
    · rw [hxr] <;> linarith
    · rw [hxi] <;> linarith
    · rw [hxi] <;> linarith
  · rw [hxr] <;> linarith
  · rw [hxr] <;> linarith
  · rw [hxi] <;> linarith
  · rintro z hz ⟨d1, d2⟩
    rw [hxr, abs_lt] at d1
    rw [hxi, abs_lt] at d2
    by_cases hzA : z.im < A
    · rw [cellSide_eq_of_ho hC hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hεss
    · rw [cellSide_eq_of_ho hC' hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hr1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hxr] <;> linarith
    · rw [hxr] <;> linarith
    · rw [hxi] <;> linarith
    · rw [hxi] <;> linarith
  · rw [hxr] <;> linarith
  · rw [hxr] <;> linarith
  · rw [hxi] <;> linarith
  · rintro z hz ⟨d1, d2⟩
    rw [hxr, abs_lt] at d1
    rw [hxi, abs_lt] at d2
    by_cases hzA : z.im < A
    · rw [cellSide_eq_of_ho hC hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hr2
    · rw [cellSide_eq_of_ho hC' hz (by linarith) (by linarith) (by linarith) (by linarith)]
      exact hεss'
  · have hsc := center_boxAt_of_center hp1 hp2 gpr gpi
    have hsc' := center_boxAt_of_center hp1' hp2' gpr' gpi'
    refine ⟨fun e => ?_, fun hsub => ?_⟩
    · have e2 := congrArg (fun b => (DyBox.center b).im) e
      simp only [hsc, hsc', hpi, hpi'] at e2
      linarith
    · obtain ⟨q, hqi, hqr⟩ : ∃ q : ℂ, q.im = A ∧ q.re = (κ + 1 / 2) * ℓ + min w w' :=
        ⟨⟨_, _⟩, rfl, rfl⟩
      have hμ0 : 0 < min w w' := lt_min hw0 hw0'
      have hμ1 := min_le_left w w'
      have hμ2 := min_le_right w w'
      have hq1 : q ∈ (boxAt (C.n + 2 * k) p).closedBox := mem1 q
        (by rw [hqr, hpr, abs_le]; constructor <;> linarith)
        (by rw [hqi, hpi, abs_le]; constructor <;> linarith)
      have hq2 : q ∈ (boxAt (C'.n + 2 * k) p').closedBox := mem2 q
        (by rw [hqr, hpr', abs_le]; constructor <;> linarith)
        (by rw [hqi, hpi', abs_le]; constructor <;> linarith)
      have e := hsub ⟨hxs, hxs'⟩ ⟨hq1, hq2⟩
      have e2 := congrArg Complex.re e
      rw [hxr, hqr] at e2
      linarith

end DZZ
end LQGMetric
