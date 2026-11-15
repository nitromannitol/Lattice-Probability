import Mathlib

/-! # Global entry into open sets for two-sided paths -/

set_option autoImplicit false

open Set MeasureTheory Classical

namespace LatticeProb

/-- The infimum of all entrance times of a two-sided path, with both infinite
endpoints available. -/
noncomputable def globalOpenEntry {Ω E : Type*} (f : Ω → ℝ → E)
    (U : Set E) (ω : Ω) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t | f ω t ∈ U})

/-- For continuous paths and open sets, rational entrance times give the same
infimum as all entrance times. -/
theorem globalOpenEntry_eq_iInf_rat {Ω E : Type*} [TopologicalSpace E]
    (f : Ω → ℝ → E) {U : Set E} (hU : IsOpen U)
    (hf : ∀ ω, Continuous (f ω)) (ω : Ω) :
    globalOpenEntry f U ω = ⨅ q : ℚ, if f ω q ∈ U then ((q : ℝ) : EReal) else ⊤ := by
  classical
  apply le_antisymm
  · refine le_iInf fun q => ?_
    split_ifs with hq
    · exact sInf_le ⟨q, hq, rfl⟩
    · exact le_top
  · apply le_sInf
    rintro x ⟨t, ht, rfl⟩
    apply le_of_forall_gt
    intro b htb
    obtain ⟨r, htr, hrb⟩ := EReal.exists_rat_btwn_of_lt htb
    have htr' : t < (r : ℝ) := EReal.coe_lt_coe_iff.mp htr
    have hopen : IsOpen ((f ω) ⁻¹' U) := hU.preimage (hf ω)
    obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ht)
    obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_min htr' htu)
    have hqU : f ω q ∈ U := hsub ⟨hlt.trans htq, (lt_min_iff.mp hq).2⟩
    calc
      (⨅ q : ℚ, if f ω q ∈ U then ((q : ℝ) : EReal) else ⊤) ≤
          ((q : ℝ) : EReal) := by simpa [hqU] using
            (iInf_le (fun q : ℚ => if f ω q ∈ U then ((q : ℝ) : EReal) else ⊤) q)
      _ ≤ ((r : ℝ) : EReal) := by exact_mod_cast (lt_min_iff.mp hq).1.le
      _ < b := hrb

/-- Global open entry is measurable from the rational evaluations of the paths. -/
theorem measurable_globalOpenEntry {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → ℝ → E) {U : Set E} (hU : IsOpen U)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ q : ℚ, Measurable fun ω => f ω q) :
    Measurable (globalOpenEntry f U) := by
  classical
  have heq : globalOpenEntry f U = fun ω =>
      ⨅ q : ℚ, if f ω q ∈ U then ((q : ℝ) : EReal) else ⊤ := by
    funext ω
    exact globalOpenEntry_eq_iInf_rat f hU hf ω
  rw [heq]
  exact Measurable.iInf fun q => Measurable.ite
    (hU.measurableSet.preimage (hm q)) measurable_const measurable_const

end LatticeProb
