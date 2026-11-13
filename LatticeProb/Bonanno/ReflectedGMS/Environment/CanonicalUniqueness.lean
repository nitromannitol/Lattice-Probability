/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.CanonicalUniqueness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws

/-! Uniqueness consequences of the existing least-interior-label encoding.
This establishes uniqueness only: it makes no assertion of existence or
measurability of a canonically relabelled similarity action. -/
set_option autoImplicit false
open Set
namespace ReflectedGMS.Code

/-- A compact cell has at most one least rational interior-hit index. -/
theorem LeastInteriorLabel.unique {K : CompactCell} {n m : ℕ}
    (hn : LeastInteriorLabel K n) (hm : LeastInteriorLabel K m) : n = m := by
  apply le_antisymm
  · exact le_of_not_gt (fun hmn => hn.2 m hmn hm.1)
  · exact le_of_not_gt (fun hnm => hm.2 n hnm hn.1)

/-- Identical compact cells in two canonical codes have the same natural label. -/
theorem label_eq_of_cell_eq {r r' : RawCode}
    (hr : CanonicalLabels r) (hr' : CanonicalLabels r')
    (v : Vertex r) (v' : Vertex r') (h : cell r v = cell r' v') :
    v.val = v'.val := by
  exact (h ▸ hr v).unique (hr' v')

/-- Canonical active cells cannot repeat inside one code. -/
theorem CanonicalLabels.cell_injective {r : RawCode} (hr : CanonicalLabels r) :
    Function.Injective (cell r) := by
  intro v w h
  exact Subtype.ext (label_eq_of_cell_eq hr hr v w h)

theorem decode_cell_injective (e : Env) : Function.Injective (decode e).cell :=
  (decode_canonicalLabels e).cell_injective

/-- A weighted-cell equivalence between canonical environments identifies the
entire raw codes, including the zero conductances at absent labels. -/
theorem env_eq_of_relabel (e e' : Env)
    (q : Vertex e.val ≃ Vertex e'.val)
    (hc : ∀ v, (decode e').cell (q v) = (decode e).cell v)
    (hg : ∀ v w, (decode e').graph.c (q v) (q w) = (decode e).graph.c v w) :
    e = e' := by
  have hlabel : ∀ v : Vertex e.val, (q v).val = v.val := by
    intro v
    exact label_eq_of_cell_eq (decode_canonicalLabels e') (decode_canonicalLabels e)
      (q v) v (hc v)
  have hslot : ∀ v : Vertex e.val, e'.val.1 v.val = e.val.1 v.val := by
    intro v
    calc
      e'.val.1 v.val = e'.val.1 (q v).val := congrArg e'.val.1 (hlabel v).symm
      _ = some (cell e'.val (q v)) := (Option.some_get (q v).property).symm
      _ = some (cell e.val v) := congrArg some (hc v)
      _ = e.val.1 v.val := Option.some_get v.property
  have hslots : ∀ n, e.val.1 n = e'.val.1 n := by
    intro n
    by_cases hn : (e.val.1 n).isSome
    · exact (hslot ⟨n, hn⟩).symm
    · by_cases hn' : (e'.val.1 n).isSome
      · let v' : Vertex e'.val := ⟨n, hn'⟩
        have hval : (q.symm v').val = n := by
          calc
            (q.symm v').val = (q (q.symm v')).val := (hlabel (q.symm v')).symm
            _ = n := congrArg Subtype.val (q.apply_symm_apply v')
        exact (hn (by simpa only [hval] using (q.symm v').property)).elim
      · exact (Option.not_isSome_iff_eq_none.mp hn).trans
          (Option.not_isSome_iff_eq_none.mp hn').symm
  apply Subtype.ext
  apply Prod.ext
  · exact funext hslots
  · funext n m
    by_cases hn : (e.val.1 n).isSome
    · by_cases hm : (e.val.1 m).isSome
      · have h := hg ⟨n, hn⟩ ⟨m, hm⟩
        change e'.val.2 (q ⟨n, hn⟩).val (q ⟨m, hm⟩).val = e.val.2 n m at h
        simpa only [hlabel] using h.symm
      · have hm0 := Option.not_isSome_iff_eq_none.mp hm
        rw [e.property.choose.absent n m (Or.inr hm0),
          e'.property.choose.absent n m (Or.inr ((hslots m).symm.trans hm0))]
    · have hn0 := Option.not_isSome_iff_eq_none.mp hn
      rw [e.property.choose.absent n m (Or.inl hn0),
        e'.property.choose.absent n m (Or.inl ((hslots n).symm.trans hn0))]

end ReflectedGMS.Code
namespace ReflectedGMS.EnvironmentLaws
open Code

/-- The bijection witnessing a fixed physical similarity is unique. -/
theorem IsSimilarityRelabel.relabel_unique {s : ℝ} {u : Plane} {hs : 0 < s}
    {e e' : Env} {q q' : Vertex e.val ≃ Vertex e'.val}
    (h : IsSimilarityRelabel s u hs e e' q)
    (h' : IsSimilarityRelabel s u hs e e' q') : q = q' := by
  apply Equiv.ext
  intro v
  apply decode_cell_injective e'
  exact (h.1 v).trans (h'.1 v).symm

/-- A source canonical environment and a physical similarity determine at most
one target canonical environment. No canonical action is assumed here. -/
theorem IsSimilarity.target_unique {s : ℝ} {u : Plane} {hs : 0 < s}
    {e e₁ e₂ : Env} (h₁ : IsSimilarity s u hs e e₁)
    (h₂ : IsSimilarity s u hs e e₂) : e₁ = e₂ := by
  obtain ⟨q₁, hc₁, hg₁⟩ := h₁
  obtain ⟨q₂, hc₂, hg₂⟩ := h₂
  apply env_eq_of_relabel e₁ e₂ (q₁.symm.trans q₂)
  · intro v
    calc
      (decode e₂).cell ((q₁.symm.trans q₂) v) =
          transformCell s u hs ((decode e).cell (q₁.symm v)) := hc₂ (q₁.symm v)
      _ = (decode e₁).cell v := by simpa only [Equiv.apply_symm_apply] using
          (hc₁ (q₁.symm v)).symm
  · intro v w
    calc
      (decode e₂).graph.c ((q₁.symm.trans q₂) v) ((q₁.symm.trans q₂) w) =
          (decode e).graph.c (q₁.symm v) (q₁.symm w) := hg₂ (q₁.symm v) (q₁.symm w)
      _ = (decode e₁).graph.c v w := by simpa only [Equiv.apply_symm_apply] using
          (hg₁ (q₁.symm v) (q₁.symm w)).symm

end ReflectedGMS.EnvironmentLaws
