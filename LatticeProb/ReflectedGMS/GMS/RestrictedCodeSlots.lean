import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet

/-! # Restricted families of coded cells -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS.ValidCodeSet

open Code

/-- A slot is near a point exactly when it is occupied by a cell meeting the open ball. -/
theorem slotNear_iff_isSome_inter_ball (r : RawCode) (q : Plane) (t : ℝ) (n : ℕ) :
    SlotNear q t (r.1 n) ↔
      (r.1 n).isSome ∧ ((slotCell r n : Set Plane) ∩ Metric.ball q t).Nonempty := by
  cases h : r.1 n with
  | none => simp [SlotNear]
  | some K =>
    rw [slotCell_of_eq_some h]
    constructor
    · rintro ⟨L, hL, hdist⟩
      have hLK : L = K := (Option.some.inj hL).symm
      subst L
      obtain ⟨x, hx, hd⟩ := (Metric.infDist_lt_iff K.nonempty).1 hdist
      exact ⟨by simp, ⟨x, hx, by simpa only [Metric.mem_ball, dist_comm] using hd⟩⟩
    · rintro ⟨_, x, hx, hball⟩
      refine ⟨K, rfl, (Metric.infDist_lt_iff K.nonempty).2 ?_⟩
      exact ⟨x, hx, by simpa only [Metric.mem_ball, dist_comm] using hball⟩

/-- The slots near a point enumerate precisely the decoded cells meeting its open ball. -/
theorem mem_decodeConfig_restrict_ball_iff (r : RawCode) (q : Plane) (t : ℝ) (K : Cell) :
    K ∈ (decodeConfig r).restrict (Metric.ball q t) ↔
      ∃ n, SlotNear q t (r.1 n) ∧ slotCell r n = K := by
  constructor
  · rintro ⟨⟨n, hn⟩, hmeet⟩
    refine ⟨n, ?_, slotCell_of_eq_some hn⟩
    apply (slotNear_iff_isSome_inter_ball r q t n).2
    exact ⟨isSome_of_eq_some hn, by rw [slotCell_of_eq_some hn]; exact hmeet⟩
  · rintro ⟨n, hnear, hK⟩
    have hmeet := ((slotNear_iff_isSome_inter_ball r q t n).1 hnear).2
    obtain ⟨L, hn, _⟩ := hnear
    have heq : L = K := (slotCell_of_eq_some hn).symm.trans hK
    subst L
    refine ⟨⟨n, hn⟩, ?_⟩
    rwa [hK] at hmeet

/-- On occupied slots of a good code, adjacency is positivity of the code coordinate. -/
theorem IsGoodCode.decodeConfig_adj_slot {r : RawCode} (hr : IsGoodCode r)
    {n m : ℕ} (hn : (r.1 n).isSome) (hm : (r.1 m).isSome) :
    (decodeConfig r).Adj (slotCell r n) (slotCell r m) ↔ 0 < r.2 n m := by
  cases hns : r.1 n with
  | none => simp [hns] at hn
  | some K =>
    cases hms : r.1 m with
    | none => simp [hms] at hm
    | some L =>
      rw [slotCell_of_eq_some hns, slotCell_of_eq_some hms]
      change 0 < (decodeConfig r).c K L ↔ 0 < r.2 n m
      rw [hr.decodeConfig_c hns hms]

end ReflectedGMS.GMS.ValidCodeSet
