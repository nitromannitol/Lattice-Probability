/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13G4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G3

/-!
# DZZ Lemma 3.13, cell geometry IV: the door between two good neighbouring cells (P2-DZZ313G)

DZZ arXiv:1807.00422 l. 1327–1331. `exists_door`: two neighbouring cells with side ratio in
`[ε, 1/ε]`, `ε = 2^{-k}`, `k ≥ 1`, share a door (`L313DoorSide` on both sides, neighbouring boxes of sides
`ε² s_𝖢`, `ε² s_𝖢'` at the middle `x` of `Λ = ∂𝖢 ∩ ∂𝖢'`). Own elementary proof (case analysis of the
contact).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- **The door** between two good neighbouring cells. -/
theorem exists_door {C C' : DyBox} (hC : IsCell m δ C) (hC' : IsCell m δ C') (hN : Neighbour C C')
    {k : ℕ} (hk : 1 ≤ k) (hr : SideRatio ((2 : ℝ)⁻¹ ^ k) C C') :
    ∃ x s s', L313DoorSide m δ k C x s ∧ L313DoorSide m δ k C' x s' ∧ Neighbour s s' := by
  obtain ⟨hne, hns⟩ := hN
  simp only [Set.Subsingleton, not_forall] at hns
  obtain ⟨z, ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩, z', ⟨⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3, f4⟩⟩, hzz⟩ :=
    hns
  have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hrs := hr.symm hε
  have flip : ∀ x s s', L313DoorSide m δ k C' x s → L313DoorSide m δ k C x s' → Neighbour s s' →
      ∃ x s s', L313DoorSide m δ k C x s ∧ L313DoorSide m δ k C' x s' ∧ Neighbour s s' :=
    fun x s s' h1 h2 h3 => ⟨x, s', s, h2, h1, h3.symm⟩
  have hs := side_pos' C
  have hs' := side_pos' C'
  by_cases hj2 : (C'.j : ℝ) * C'.side < (C.j + 1) * C.side
  · by_cases hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side
    · by_cases hk2 : (C'.k : ℝ) * C'.side < (C.k + 1) * C.side
      · by_cases hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side
        · exfalso
          rcases le_total C'.n C.n with hle | hle
          · have u := dy_nested_real (n := C.n) (n' := C'.n) hle hj1 hj2
            have v := dy_nested_real (n := C.n) (n' := C'.n) hle hk1 hk2
            have hsub : C.closedBox ⊆ C'.closedBox := by
              rintro q ⟨q1, q2, q3, q4⟩
              exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
            exact hne (eq_of_sub_cell hC hC' le_rfl hle hsub)
          · have u := dy_nested_real (n := C'.n) (n' := C.n) hle hj2 hj1
            have v := dy_nested_real (n := C'.n) (n' := C.n) hle hk2 hk1
            have hsub : C'.closedBox ⊆ C.closedBox := by
              rintro q ⟨q1, q2, q3, q4⟩
              exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
            exact hne (eq_of_sub_cell hC' hC le_rfl hle hsub).symm
        · -- `𝖢'` below `𝖢`
          have ha : ((C'.k : ℝ) + 1) * C'.side = C.k * C.side := by
            push_neg at hk1; linarith
          obtain ⟨x, s, s', h1, h2, h3⟩ := door_horiz hC' hC hk hrs ha
            (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
            (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
          exact flip x s s' h1 h2 h3
      · -- `𝖢` below `𝖢'`
        have ha : ((C.k : ℝ) + 1) * C.side = C'.k * C'.side := by
          push_neg at hk2; linarith
        exact door_horiz hC hC' hk hr ha
          (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
          (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
    · -- `𝖢'` left of `𝖢`
      have ha : ((C'.j : ℝ) + 1) * C'.side = C.j * C.side := by
        push_neg at hj1; linarith
      obtain ⟨x, s, s', h1, h2, h3⟩ := door_vert hC' hC hk hrs ha
        (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
        (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
      exact flip x s s' h1 h2 h3
  · -- `𝖢` left of `𝖢'`
    have ha : ((C.j : ℝ) + 1) * C.side = C'.j * C'.side := by
      push_neg at hj2; linarith
    exact door_vert hC hC' hk hr ha
      (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))
      (by by_contra hh; push_neg at hh; exact hzz (Complex.ext (by linarith) (by linarith)))

end DZZ
end LQGMetric
