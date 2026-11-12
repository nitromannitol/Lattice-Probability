/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_10ProofScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10Sq
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6Law
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.10, step (iii): scaling (T:957–962)

"The occurrence of the event in (2.11) is unaffected by re-scaling `D_h^ε` by a constant factor.
By Lemma 2.6 applied with `Rr` in place of `r`, (2.11) implies (2.12) for each fixed `r`."

* `sqBdyEvent_scale`: if `D^{ε/ρ}_y(z,w) = c D^ε_x(ρz, ρw)` with `c ∈ (0,∞)` (the identity of
  `lem2_6`), then the event at scale `s` for `(y, ε/ρ)` is the event at scale `ρ s` for `(x, ε)`.
* `measure_sqBdyEvent_eq_of_map_eq`: the probability of the event depends only on the law of the
  field (whole-plane GFFs): the event is a.s. equal to a measurable set of fields, obtained
  through `LFPP.lfppDistChain` on countable dense subsets (continuity of `D^ε`,
  `LFPP.continuous_lfppDReal`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

theorem mem_sqC_mul_iff {ρ s : ℝ} (hρ : 0 < ρ) {z : ℂ} :
    (ρ : ℂ) * z ∈ sqC (ρ * s) 0 ↔ z ∈ sqC s 0 := by
  rw [mem_sqC_iff, mem_sqC_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem sqC_mul_eq_image {ρ s : ℝ} (hρ : 0 < ρ) :
    sqC (ρ * s) 0 = (Homeomorph.mulLeft₀ (ρ : ℂ) (by exact_mod_cast hρ.ne')) '' sqC s 0 := by
  have hne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  ext x
  simp only [mem_image, Homeomorph.coe_mulLeft₀]
  constructor
  · intro hx
    refine ⟨(ρ : ℂ)⁻¹ * x, ?_, mul_inv_cancel_left₀ hne x⟩
    rw [← mem_sqC_mul_iff hρ, mul_inv_cancel_left₀ hne]
    exact hx
  · rintro ⟨z, hz, rfl⟩
    exact (mem_sqC_mul_iff hρ).2 hz

/-- **the event of (2.10) under scaling** -/
theorem sqBdyEvent_scale {ξ ε C s R ρ : ℝ} (hρ : 0 < ρ) {x y : DistC} {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (hxy : ∀ z w, lfppDistE ξ (ε / ρ) y z w =
      c * lfppDistE ξ ε x ((ρ : ℂ) * z) ((ρ : ℂ) * w)) :
    sqBdyEvent ξ (ε / ρ) C s R y ↔ sqBdyEvent ξ ε C (ρ * s) R x := by
  have hne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set T := Homeomorph.mulLeft₀ (ρ : ℂ) hne
  have e1 : sqC (ρ * s) 0 = T '' sqC s 0 := sqC_mul_eq_image hρ
  have e2 : frontier (sqC (R * (ρ * s)) 0) = T '' frontier (sqC (R * s) 0) := by
    rw [T.image_frontier, ← sqC_mul_eq_image hρ, mul_left_comm]
  have hT : ∀ z, T z = (ρ : ℂ) * z := fun z => rfl
  unfold sqBdyEvent
  rw [e1, e2]
  simp only [iSup_image, iInf_image, hT, hxy]
  have hsup : (⨆ u ∈ sqC s 0, ⨆ v ∈ sqC s 0, c * lfppDistE ξ ε x (↑ρ * u) (↑ρ * v)) =
      c * ⨆ u ∈ sqC s 0, ⨆ v ∈ sqC s 0, lfppDistE ξ ε x (↑ρ * u) (↑ρ * v) := by
    simp only [ENNReal.mul_iSup]
  have hinf : (⨅ u ∈ sqC s 0, ⨅ v ∈ frontier (sqC (R * s) 0),
      c * lfppDistE ξ ε x (↑ρ * u) (↑ρ * v)) =
      c * ⨅ u ∈ sqC s 0, ⨅ v ∈ frontier (sqC (R * s) 0), lfppDistE ξ ε x (↑ρ * u) (↑ρ * v) := by
    simp only [ENNReal.mul_iInf_of_ne hc0 hct]
  rw [hsup, hinf, mul_left_comm, ENNReal.mul_lt_mul_iff_right hc0 hct]

/-- a continuous `[0,∞]`-valued function has the same double sup over sets as over dense subsets -/
theorem biSup_biSup_eq_of_dense {f : ℂ × ℂ → ℝ≥0∞} (hf : Continuous f) {A B c d : Set ℂ}
    (hc : c ⊆ A) (hA : A ⊆ closure c) (hd : d ⊆ B) (hB : B ⊆ closure d) :
    (⨆ u ∈ A, ⨆ v ∈ B, f (u, v)) = ⨆ u ∈ c, ⨆ v ∈ d, f (u, v) := by
  refine le_antisymm (iSup₂_le fun u hu => iSup₂_le fun v hv => ?_)
    (iSup₂_le fun u hu => iSup₂_le fun v hv =>
      le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ B, f (u, v)) u (hc hu)
        (le_iSup₂_of_le (f := fun v _ => f (u, v)) v (hd hv) le_rfl))
  have hcl : closure (c ×ˢ d) ⊆ {p | f p ≤ ⨆ u ∈ c, ⨆ v ∈ d, f (u, v)} :=
    closure_minimal (fun p hp => le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ d, f (u, v)) p.1 hp.1
      (le_iSup₂_of_le (f := fun v _ => f (p.1, v)) p.2 hp.2 le_rfl))
      (isClosed_le hf continuous_const)
  exact hcl (by rw [closure_prod_eq]; exact ⟨hA hu, hB hv⟩)

theorem biInf_biInf_eq_of_dense {f : ℂ × ℂ → ℝ≥0∞} (hf : Continuous f) {A B c d : Set ℂ}
    (hc : c ⊆ A) (hA : A ⊆ closure c) (hd : d ⊆ B) (hB : B ⊆ closure d) :
    (⨅ u ∈ A, ⨅ v ∈ B, f (u, v)) = ⨅ u ∈ c, ⨅ v ∈ d, f (u, v) := by
  refine le_antisymm
    (le_iInf₂ fun u hu => le_iInf₂ fun v hv =>
      iInf₂_le_of_le (f := fun u _ => ⨅ v ∈ B, f (u, v)) u (hc hu)
        (iInf₂_le_of_le (f := fun v _ => f (u, v)) v (hd hv) le_rfl))
    (le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_)
  have hcl : closure (c ×ˢ d) ⊆ {p | (⨅ u ∈ c, ⨅ v ∈ d, f (u, v)) ≤ f p} :=
    closure_minimal (fun p hp => iInf₂_le_of_le (f := fun u _ => ⨅ v ∈ d, f (u, v)) p.1 hp.1
      (iInf₂_le_of_le (f := fun v _ => f (p.1, v)) p.2 hp.2 le_rfl))
      (isClosed_le continuous_const hf)
  exact hcl (by rw [closure_prod_eq]; exact ⟨hA hu, hB hv⟩)

theorem continuous_lfppDistE_uncurry {ξ ε : ℝ} {x : DistC} (hc : Continuous (heatMollify ε x)) :
    Continuous fun p : ℂ × ℂ => lfppDistE ξ ε x p.1 p.2 := by
  have e : (fun p : ℂ × ℂ => lfppDistE ξ ε x p.1 p.2) =
      fun p => ENNReal.ofReal (lfppDReal ξ (heatMollify ε x) p) := by
    funext p
    rw [lfppDReal, ENNReal.ofReal_toReal (lfppD_ne_top hc p.1 p.2), lfppDistE_eq_lfppDOn]
  rw [e]
  exact ENNReal.continuous_ofReal.comp (continuous_lfppDReal hc)

/-- the event of (2.10) as a measurable set of fields, up to fields with discontinuous
mollification -/
theorem exists_measurableSet_sqBdyEvent (ξ ε C s R : ℝ) :
    ∃ E : Set DistC, MeasurableSet E ∧ ∀ x : DistC, Continuous (heatMollify ε x) →
      (sqBdyEvent ξ ε C s R x ↔ x ∈ E) := by
  obtain ⟨c1, hc1, hc1c, hc1d⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (sqC s 0)).exists_countable_dense_subset
  obtain ⟨c2, hc2, hc2c, hc2d⟩ := (TopologicalSpace.IsSeparable.of_separableSpace
    (frontier (sqC (R * s) 0))).exists_countable_dense_subset
  refine ⟨{x | (⨆ u ∈ c1, ⨆ v ∈ c1, lfppDistChain ξ ε x u v) <
      ENNReal.ofReal C⁻¹ * ⨅ u ∈ c1, ⨅ v ∈ c2, lfppDistChain ξ ε x u v}, ?_, ?_⟩
  · exact measurableSet_lt (Measurable.biSup c1 hc1c fun u _ =>
        Measurable.biSup c1 hc1c fun v _ => measurable_lfppDistChain ξ ε u v)
      ((Measurable.biInf c1 hc1c fun u _ =>
        Measurable.biInf c2 hc2c fun v _ => measurable_lfppDistChain ξ ε u v).const_mul _)
  · intro x hx
    have hf := continuous_lfppDistE_uncurry (ξ := ξ) hx
    unfold sqBdyEvent
    rw [biSup_biSup_eq_of_dense hf hc1 hc1d hc1 hc1d, biInf_biInf_eq_of_dense hf hc1 hc1d hc2 hc2d]
    simp only [lfppDistE_eq_chain hx, mem_ofPred_eq]

/-- the probability of the event of (2.10) depends only on the law of the (whole-plane GFF)
field -/
theorem measure_sqBdyEvent_eq_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → DistC} (hX : IsWholePlaneGFF X P) (hY : IsWholePlaneGFF Y P)
    (hlaw : P.map X = P.map Y) (ξ : ℝ) {ε : ℝ} (hε : ε ≠ 0) (C s R : ℝ) :
    P {ω | sqBdyEvent ξ ε C s R (X ω)} = P {ω | sqBdyEvent ξ ε C s R (Y ω)} := by
  obtain ⟨E, hEm, hE⟩ := exists_measurableSet_sqBdyEvent ξ ε C s R
  have k : ∀ Z : Ω → DistC, IsWholePlaneGFF Z P →
      P {ω | sqBdyEvent ξ ε C s R (Z ω)} = P.map Z E := fun Z hZ => by
    rw [Measure.map_apply hZ.measurable hEm]
    refine measure_congr ?_
    filter_upwards [hZ.ae_tendstoLocallyUniformly_heatMollify ε hε] with ω hω
    exact propext (hE _ hω.2)
  rw [k X hX, k Y hY, hlaw]

end LQGMetric.DFGPS
