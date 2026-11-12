/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.LQGDimension.LFPP.CircCovDominated
import LatticeProb.Bonanno.LQGDimension.LFPP.SimilarityCov

/-!
# Node `MT` (`Draft.RecordMeanTransfer`)

We prove `Blueprint.Draft.RecordMeanTransfer` from `SegCombLaw` (`P1`), `SimilarityCov` (`SIM`)
and `CircCovDominated` (`L31d`); Sudakov–Fernique and the Gram bridge are already proved in
`LQGDimension.Gaussian.*`.

## Strategy

* `cfgVal φ δ k c = δ^{-1/2} ⟨φ, cfgComb c⟩ - k`, and `cfgComb (cfgMap s c)` is the image of
  `cfgComb c` under the similarity `simMap s` (similarities scale all lengths equally).
* By `P1`, `(⟨h_ε, cfgComb (cfgMap s c)⟩)_{c ∈ F₀}` is the Gaussian vector with covariance
  `circCov ε`.  If that matrix is positive semidefinite it is a Gram matrix; otherwise
  `multivariateGaussian` is the Dirac mass at `0` and the vector is the zero family.
* Canonical distances: `circCov ε (d.image σ) (d.image σ) = circCov (ε/|α|) d d ≤ logCov d d`
  for the zero-mass nondegenerate differences `d = cfgComb c - cfgComb c'` (`SIM`, `L31d`), so
  Sudakov–Fernique with drift `-k` concludes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.MeanTransfer

open Blueprint.Draft

/-! ## Algebra of segment combinations -/

/-- The weighted double sum of a kernel on segment endpoints. -/
def dsum (K : ℂ × ℂ → ℂ × ℂ → ℝ) (c c' : SegComb) : ℝ :=
  (c.map fun p => (c'.map fun p' => p.1 * p'.1 * K p.2 p'.2).sum).sum

/-- Negation of all weights. -/
def negW (c : SegComb) : SegComb := c.map fun p => (-p.1, p.2)

lemma sub_eq (c c' : SegComb) : c.sub c' = c ++ negW c' := rfl

lemma dsum_append_left (K : ℂ × ℂ → ℂ × ℂ → ℝ) (c d e : SegComb) :
    dsum K (c ++ d) e = dsum K c e + dsum K d e := by
  simp [dsum, List.map_append, List.sum_append]

lemma dsum_append_right (K : ℂ × ℂ → ℂ × ℂ → ℝ) (c d e : SegComb) :
    dsum K c (d ++ e) = dsum K c d + dsum K c e := by
  unfold dsum
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at ih ⊢
    rw [ih]
    ring

lemma dsum_negW_left (K : ℂ × ℂ → ℂ × ℂ → ℝ) (c d : SegComb) :
    dsum K (negW c) d = -dsum K c d := by
  unfold dsum negW
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, neg_add]
    congr 1
    clear ih
    induction d with
    | nil => simp
    | cons q d ih' =>
      simp only [List.map_cons, List.sum_cons, ih']
      ring

lemma dsum_negW_right (K : ℂ × ℂ → ℂ × ℂ → ℝ) (c d : SegComb) :
    dsum K c (negW d) = -dsum K c d := by
  unfold dsum negW
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, neg_add]
    congr 1
    clear ih
    induction d with
    | nil => simp
    | cons q d ih' =>
      simp only [List.map_cons, List.sum_cons, ih']
      ring

lemma dsum_sub_sub (K : ℂ × ℂ → ℂ × ℂ → ℝ) (A B : SegComb) :
    dsum K (A.sub B) (A.sub B) = dsum K A A - dsum K A B - dsum K B A + dsum K B B := by
  rw [sub_eq, dsum_append_left, dsum_append_right, dsum_append_right, dsum_negW_left,
    dsum_negW_left, dsum_negW_right, dsum_negW_right]
  ring

lemma circCov_eq_dsum (ε : ℝ) (c c' : SegComb) :
    c.circCov ε c' = dsum (fun e e' => segCircCov ε e.1 e.2 e'.1 e'.2) c c' := rfl

lemma logCov_eq_dsum (c c' : SegComb) :
    c.logCov c' = dsum (fun e e' => segLogPair e.1 e.2 e'.1 e'.2) c c' := rfl

lemma circCov_sub_sub (ε : ℝ) (A B : SegComb) :
    (A.sub B).circCov ε (A.sub B) =
      A.circCov ε A - A.circCov ε B - B.circCov ε A + B.circCov ε B := by
  simp only [circCov_eq_dsum]
  exact dsum_sub_sub _ A B

lemma logCov_sub_sub (A B : SegComb) :
    (A.sub B).logCov (A.sub B) = A.logCov A - A.logCov B - B.logCov A + B.logCov B := by
  simp only [logCov_eq_dsum]
  exact dsum_sub_sub _ A B

lemma dsum_smul_left (K : ℂ × ℂ → ℂ × ℂ → ℝ) (r : ℝ) (c d : SegComb) :
    dsum K (c.smul r) d = r * dsum K c d := by
  unfold dsum SegComb.smul
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    clear ih
    induction d with
    | nil => simp
    | cons q d ih' =>
      simp only [List.map_cons, List.sum_cons, ih']
      ring

lemma dsum_smul_right (K : ℂ × ℂ → ℂ × ℂ → ℝ) (r : ℝ) (c d : SegComb) :
    dsum K c (d.smul r) = r * dsum K c d := by
  unfold dsum SegComb.smul
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    clear ih
    induction d with
    | nil => simp
    | cons q d ih' =>
      simp only [List.map_cons, List.sum_cons, ih']
      ring

lemma circCov_smul (ε r : ℝ) (c d : SegComb) :
    (c.smul r).circCov ε (d.smul r) = r * r * c.circCov ε d := by
  simp only [circCov_eq_dsum, dsum_smul_left, dsum_smul_right]
  ring

lemma avg_smul (φ : ℂ → ℝ) (r : ℝ) (c : SegComb) : (c.smul r).avg φ = r * c.avg φ := by
  simp only [SegComb.avg, SegComb.smul, List.map_map, Function.comp_def, mul_assoc,
    List.sum_map_mul_left]

lemma list_sum_map_neg {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma avg_sub (φ : ℂ → ℝ) (c c' : SegComb) : (c.sub c').avg φ = c.avg φ - c'.avg φ := by
  simp only [SegComb.avg, SegComb.sub, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, neg_mul, list_sum_map_neg]
  ring

lemma cfgVal_eq (φ : ℂ → ℝ) (δ : ℝ) (k : ℕ) (c : Config) :
    cfgVal φ δ k c = δ ^ (-(1 / 2 : ℝ)) * (cfgComb c).avg φ - k := by
  rw [cfgVal, cfgComb, avg_sub]
  rfl

lemma mass_sub (c c' : SegComb) : (c.sub c').mass = c.mass - c'.mass := by
  simp only [SegComb.mass, SegComb.sub, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, list_sum_map_neg]
  ring

lemma nondeg_sub {c c' : SegComb} (hc : c.Nondeg) (hc' : c'.Nondeg) : (c.sub c').Nondeg := by
  intro p hp hw
  simp only [SegComb.sub, List.mem_append, List.mem_map] at hp
  rcases hp with hp | ⟨q, hq, rfl⟩
  · exact hc p hp hw
  · exact hc' q hq (neg_ne_zero.1 hw)

lemma image_sub (T : ℂ → ℂ) (c c' : SegComb) :
    (c.sub c').image T = (c.image T).sub (c'.image T) := by
  simp [SegComb.image, SegComb.sub, List.map_append, List.map_map, Function.comp_def]

/-! ## Polygons under similarities -/

lemma edges_map (T : ℂ → ℂ) (z : List ℂ) : edges (z.map T) = (edges z).map (Prod.map T T) := by
  simp only [edges]
  rw [← List.map_tail, List.zip_map]

lemma norm_simMap_sub (s : ℂ × ℂ) (u v : ℂ) :
    ‖simMap s u - simMap s v‖ = ‖s.1‖ * ‖u - v‖ := by
  rw [simMap, simMap, show s.1 * u + s.2 - (s.1 * v + s.2) = s.1 * (u - v) by ring, norm_mul]

lemma polyLen_map (s : ℂ × ℂ) (z : List ℂ) : polyLen (z.map (simMap s)) = ‖s.1‖ * polyLen z := by
  simp only [polyLen, edges_map, List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd,
    norm_simMap_sub, List.sum_map_mul_left]

lemma polyComb_map (s : ℂ × ℂ) (hs : s.1 ≠ 0) (z : List ℂ) :
    polyComb (z.map (simMap s)) = (polyComb z).image (simMap s) := by
  have hn : ‖s.1‖ ≠ 0 := norm_ne_zero_iff.2 hs
  simp only [polyComb, SegComb.image, edges_map, List.map_map, Function.comp_def, Prod.map_fst,
    Prod.map_snd, norm_simMap_sub, polyLen_map]
  exact List.map_congr_left fun e _ => by rw [mul_div_mul_left _ _ hn]

lemma cfgComb_cfgMap (s : ℂ × ℂ) (hs : s.1 ≠ 0) (c : Config) :
    cfgComb (cfgMap s c) = (cfgComb c).image (simMap s) := by
  rw [cfgComb, cfgComb, cfgMap, image_sub, polyComb_map s hs, polyComb_map s hs]

lemma mass_polyComb {z : List ℂ} (hz : 0 < polyLen z) : (polyComb z).mass = 1 := by
  simp only [SegComb.mass, polyComb, List.map_map, Function.comp_def, div_eq_mul_inv,
    List.sum_map_mul_right]
  rw [← div_eq_mul_inv]
  exact div_self hz.ne'

lemma nondeg_polyComb (z : List ℂ) : (polyComb z).Nondeg := by
  intro p hp hw
  simp only [polyComb, List.mem_map] at hp
  obtain ⟨e, _, rfl⟩ := hp
  intro h
  apply hw
  simp only at h ⊢
  rw [h, sub_self, norm_zero, zero_div]

lemma cfgComb_mass_nondeg {c : Config} (hc : 0 < polyLen c.1 ∧ 0 < polyLen c.2) :
    (cfgComb c).mass = 0 ∧ (cfgComb c).Nondeg := by
  refine ⟨?_, nondeg_sub (nondeg_polyComb _) (nondeg_polyComb _)⟩
  rw [cfgComb, mass_sub, mass_polyComb hc.1, mass_polyComb hc.2, sub_self]

/-! ## Suprema over an image -/

lemma iSup_image_eq {α β : Type*} {_ : DecidableEq β} (F : Finset α) (hF : F.Nonempty) (g : α → β)
    (f : β → ℝ) : (⨆ c : F.image g, f c) = ⨆ c : F, f (g c) := by
  have hne : Nonempty (F.image g) := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨⟨g x, Finset.mem_image_of_mem g hx⟩⟩
  have hne' : Nonempty F := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨⟨x, hx⟩⟩
  refine le_antisymm (ciSup_le fun c => ?_) (ciSup_le fun c => ?_)
  · obtain ⟨x, hx, hxc⟩ := Finset.mem_image.1 c.2
    have : f c = f (g x) := by rw [hxc]
    rw [this]
    exact le_ciSup (Finite.bddAbove_range (fun c : F => f (g c))) ⟨x, hx⟩
  · exact le_ciSup (Finite.bddAbove_range (fun c : F.image g => f c))
      ⟨g c, Finset.mem_image_of_mem g c.2⟩

/-! ## Gaussian expected maxima -/

lemma integral_gaussVecLaw {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) (b : ι → ℝ) :
    ∫ y, (⨆ i : F, y i + b i) ∂(gaussVecLaw F C) = gaussianExpectedMax F C b := by
  have hφ : Continuous fun (x : EuclideanSpace ℝ F) (i : F) => x i := PiLp.continuous_ofLp 2 _
  unfold gaussVecLaw gaussianExpectedMax
  rw [integral_map hφ.aemeasurable]
  exact (Measurable.iSup fun i => by fun_prop).aestronglyMeasurable

lemma gaussianExpectedMax_of_not_psd {ι : Type*} (F : Finset ι) (hF : F.Nonempty)
    (C : ι → ι → ℝ) (b : ℝ) (h : ¬ PSDOn F C) : gaussianExpectedMax F C (fun _ => b) = b := by
  have : Nonempty F := hF.to_subtype
  unfold gaussianExpectedMax
  unfold PSDOn at h
  rw [multivariateGaussian_of_not_posSemidef _ h, integral_dirac]
  simp

lemma vecExpectedMax_zero {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (hF : F.Nonempty)
    (b : ℝ) : vecExpectedMax F (fun _ => (0 : E)) (fun _ => b) = b := by
  have : Nonempty F := hF.to_subtype
  simp [vecExpectedMax]

lemma norm_sub_sq_of_gram {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : Finset ι} {v : ι → E} {C : ι → ι → ℝ} (hv : ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = C i j)
    {i j : ι} (hi : i ∈ F) (hj : j ∈ F) :
    ‖v i - v j‖ ^ 2 = C i i - C i j - C j i + C j j := by
  have e1 := hv i hi j hj
  have e2 := hv j hj i hi
  rw [real_inner_comm] at e2
  rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    hv i hi i hi, hv j hj j hj]
  linarith

end LQGDimension.MeanTransfer

namespace LQGDimension

open Blueprint.Draft MeanTransfer

/-- **Node `MT`** (`Blueprint.Draft.RecordMeanTransfer`), from `P1`, `SIM` and `L31d`. -/
theorem recordMeanTransfer_of (hP1 : Blueprint.Draft.SegCombLaw)
    (hSIM : Blueprint.Draft.SimilarityCov) (hD : Blueprint.Draft.CircCovDominated) :
    Blueprint.Draft.RecordMeanTransfer := by
  intro Ω _ P h hG ε hε δ hδ s hs k F₀ hF₀
  obtain ⟨α, β⟩ := s
  simp only at hs
  rcases F₀.eq_empty_or_nonempty with rfl | hne
  · simp [gaussianExpectedMax]
  set a : ℝ := δ ^ (-(1 / 2 : ℝ)) with ha
  have haa : a * a = δ⁻¹ := by
    rw [ha, ← Real.rpow_add hδ, show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  have hzm : ∀ c ∈ F₀, (cfgComb c).mass = 0 ∧ (cfgComb c).Nondeg := fun c hc =>
    cfgComb_mass_nondeg (hF₀ c hc)
  -- Gram vectors for the log kernel
  obtain ⟨w, hw⟩ := exists_gram_of_psdOn F₀ (fun c c' => (cfgComb c).logCov (cfgComb c'))
    (hD.2 Config F₀ (fun c => cfgComb c) hzm)
  have hRHS : gaussianExpectedMax F₀ (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
      (fun _ => -(k : ℝ)) = vecExpectedMax F₀ (fun c => a • w c) (fun _ => -(k : ℝ)) := by
    rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
    refine gaussianExpectedMax_congr F₀ _ fun i hi j hj => ?_
    simp only [real_inner_smul_left, real_inner_smul_right, hw i hi j hj]
    rw [← mul_assoc, haa]
  rw [hRHS]
  -- the circle covariances of the transported configurations
  set Cc : Config → Config → ℝ := fun c c' =>
    (cfgComb (cfgMap (α, β) c)).circCov ε (cfgComb (cfgMap (α, β) c')) with hCc
  have hdist : ∀ i ∈ F₀, ∀ j ∈ F₀, Cc i i - Cc i j - Cc j i + Cc j j ≤ ‖w i - w j‖ ^ 2 := by
    intro i hi j hj
    obtain ⟨hmi, hni⟩ := hzm i hi
    obtain ⟨hmj, hnj⟩ := hzm j hj
    set D := (cfgComb i).sub (cfgComb j) with hDdef
    have hmD : D.mass = 0 := by rw [hDdef, mass_sub, hmi, hmj, sub_self]
    have hnD : D.Nondeg := nondeg_sub hni hnj
    have h1 : Cc i i - Cc i j - Cc j i + Cc j j =
        (D.image (simMap (α, β))).circCov ε (D.image (simMap (α, β))) := by
      simp only [hCc]
      rw [hDdef, image_sub, ← cfgComb_cfgMap (α, β) hs i, ← cfgComb_cfgMap (α, β) hs j,
        circCov_sub_sub]
    have h2 := (hSIM α β hs D D hmD hmD hnD hnD).2 ε hε
    have h3 := hD.1 (ε / ‖α‖) (div_pos hε (norm_pos_iff.2 hs)) D hmD hnD
    have h4 : D.logCov D = ‖w i - w j‖ ^ 2 := by
      rw [hDdef, logCov_sub_sub, norm_sub_sq_of_gram hw hi hj]
    rw [h1, h2, ← h4]
    exact h3
  -- the law of the transported local variables
  set cc : Config → SegComb := fun c => (cfgComb (cfgMap (α, β) c)).smul a with hcc
  have hlaw := hP1 Ω P h hG ε hε Config F₀ cc
  have hgm : Measurable fun y : F₀ → ℝ => ⨆ i : F₀, y i + (-(k : ℝ)) :=
    Measurable.iSup fun i => by fun_prop
  have e1 : ∫ ω, (⨆ i : F₀, (cc i).avg (fun z => h ε z ω) + (-(k : ℝ))) ∂P =
      ∫ y, (⨆ i : F₀, y i + (-(k : ℝ))) ∂(gaussVecLaw F₀ (fun i j => (cc i).circCov ε (cc j))) :=
    hlaw.integral_comp hgm.aestronglyMeasurable
  have e2 : ∫ y, (⨆ i : F₀, y i + (-(k : ℝ))) ∂(gaussVecLaw F₀
      (fun i j => (cc i).circCov ε (cc j))) =
      gaussianExpectedMax F₀ (fun i j => (cc i).circCov ε (cc j)) (fun _ => -(k : ℝ)) :=
    integral_gaussVecLaw F₀ (fun i j => (cc i).circCov ε (cc j)) (fun _ => -(k : ℝ))
  have hLHS : ∫ ω, (⨆ c : F₀.image (cfgMap (α, β)), cfgVal (fun z => h ε z ω) δ k c) ∂P =
      gaussianExpectedMax F₀ (fun i j => (cc i).circCov ε (cc j)) (fun _ => -(k : ℝ)) := by
    rw [← e2, ← e1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    show (⨆ c : F₀.image (cfgMap (α, β)), cfgVal (fun z => h ε z ω) δ k c) =
      ⨆ i : F₀, (cc i).avg (fun z => h ε z ω) + (-(k : ℝ))
    rw [iSup_image_eq F₀ hne]
    simp only [hcc, ha, cfgVal_eq, avg_smul, sub_eq_add_neg]
  rw [hLHS]
  have hCcs : ∀ i j, (cc i).circCov ε (cc j) = a * a * Cc i j := fun i j => by
    simp only [hcc, hCc, circCov_smul]
  by_cases hpsd : PSDOn F₀ (fun i j => (cc i).circCov ε (cc j))
  · obtain ⟨v, hv, hvb⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax F₀ _ hpsd
    rw [hvb]
    refine sudakovFernique Config _ _ F₀ v (fun c => a • w c) _ fun i hi j hj => ?_
    show ‖v i - v j‖ ≤ ‖a • w i - a • w j‖
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    have hsq : ‖v i - v j‖ ^ 2 ≤ (|a| * ‖w i - w j‖) ^ 2 := by
      rw [norm_sub_sq_of_gram hv hi hj, hCcs, hCcs, hCcs, hCcs, mul_pow, sq_abs]
      have := hdist i hi j hj
      have ha2 : 0 ≤ a * a := mul_self_nonneg a
      calc a * a * Cc i i - a * a * Cc i j - a * a * Cc j i + a * a * Cc j j
          = a * a * (Cc i i - Cc i j - Cc j i + Cc j j) := by ring
        _ ≤ a * a * ‖w i - w j‖ ^ 2 := mul_le_mul_of_nonneg_left this ha2
        _ = a ^ 2 * ‖w i - w j‖ ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  · rw [gaussianExpectedMax_of_not_psd F₀ hne _ _ hpsd]
    calc -(k : ℝ) = vecExpectedMax F₀ (fun _ => (0 : EuclideanSpace ℝ F₀)) (fun _ => -(k : ℝ)) :=
          (vecExpectedMax_zero F₀ hne _).symm
      _ ≤ _ := sudakovFernique Config _ _ F₀ _ (fun c => a • w c) _ fun i _ j _ => by simp

/-- **Node `MT`** with the proved nodes `P1` (`segCombLaw`) and `L31d` (`circCovDominated`)
plugged in: only `SimilarityCov` remains as a hypothesis. -/
theorem recordMeanTransfer_of_similarityCov (hSIM : Blueprint.Draft.SimilarityCov) :
    Blueprint.Draft.RecordMeanTransfer :=
  recordMeanTransfer_of segCombLaw hSIM circCovDominated

/-- **Node `MT`** (`Blueprint.Draft.RecordMeanTransfer`), unconditionally: `P1`
(`segCombLaw`), `SIM` (`similarityCov`) and `L31d` (`circCovDominated`) are all proved. -/
theorem recordMeanTransfer : Blueprint.Draft.RecordMeanTransfer :=
  recordMeanTransfer_of_similarityCov similarityCov

end LQGDimension
