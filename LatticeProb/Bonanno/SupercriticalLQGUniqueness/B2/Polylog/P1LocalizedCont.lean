/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedCont at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedDef
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarCont

 
















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 

 
def epsOf (v : ℝ) : ℝ := Real.exp (-Real.exp v)

lemma epsOf_mem (v : ℝ) : epsOf v ∈ Ioo (0 : ℝ) 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.exp_pos v))⟩

lemma log_inv_epsOf (v : ℝ) : Real.log (epsOf v)⁻¹ = Real.exp v := by
  rw [epsOf, ← Real.exp_neg, neg_neg, Real.log_exp]

lemma plRad_epsOf (q v : ℝ) : plRad q (epsOf v) = Real.exp (q * v - Real.exp v) := by
  rw [plRad, log_inv_epsOf, Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp, epsOf,
    ← Real.exp_add]
  congr 1; ring

lemma plRad_sq_epsOf (q v : ℝ) :
    plRad q (epsOf v) ^ 2 = Real.exp (2 * (q * v - Real.exp v)) := by
  rw [plRad_epsOf, ← Real.exp_nat_mul]; norm_num

 
def vOf (ε : ℝ) : ℝ := Real.log (Real.log ε⁻¹)

lemma epsOf_vOf {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : epsOf (vOf ε) = ε := by
  rw [epsOf, vOf, Real.exp_log (log_inv_pos hε), Real.log_inv, neg_neg, Real.exp_log hε.1]

lemma continuousOn_vOf : ContinuousOn vOf (Ioo (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun ε : ℝ => Real.log ε⁻¹) (Ioo (0 : ℝ) 1) :=
    Real.continuousOn_log.comp (continuousOn_inv₀.mono fun ε hε => (ne_of_gt hε.1))
      fun ε hε => inv_ne_zero (ne_of_gt hε.1)
  exact Real.continuousOn_log.comp h1 fun ε hε => (log_inv_pos hε).ne'

 

 
def plKer (q : ℝ) (x : ℝ × ℂ) (w : ℂ) : ℝ :=
  locProf (2 * (q * x.1 - Real.exp x.1)) (x.2 - w) * heatKernel (epsOf x.1 ^ 2 / 2) x.2 w

lemma plBump_eq_locProf (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (y : ℂ) :
    plBump q ε hε y = locProf (Real.log (plRad q ε ^ 2)) y :=
  locBump_eq_locProf _ y

lemma plBump_epsOf (q v : ℝ) (y : ℂ) :
    plBump q (epsOf v) (epsOf_mem v) y = locProf (2 * (q * v - Real.exp v)) y := by
  rw [plBump_eq_locProf, plRad_sq_epsOf, Real.log_exp]

lemma plTest_epsOf_apply (q : ℝ) (x : ℝ × ℂ) (w : ℂ) :
    plTest q (epsOf x.1) (epsOf_mem x.1) x.2 w = plKer q x w := by
  rw [plTest_apply, plBump_epsOf]; rfl

lemma contDiff_epsOf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) epsOf :=
  Real.contDiff_exp.comp Real.contDiff_exp.neg

lemma contDiff_plKer (q : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (plKer q)) := by
  unfold Function.uncurry plKer heatKernel
  have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : (ℝ × ℂ) × ℂ => p.1.1 :=
    contDiff_fst.comp contDiff_fst
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : (ℝ × ℂ) × ℂ => epsOf p.1.1 ^ 2 / 2 :=
    ((contDiff_epsOf.comp hv).pow 2).div_const _
  have hspos : ∀ p : (ℝ × ℂ) × ℂ, 0 < epsOf p.1.1 ^ 2 / 2 := fun p => by
    have := (epsOf_mem p.1.1).1; positivity
  refine (contDiff_locProf.comp ((contDiff_const.mul ((contDiff_const.mul hv).sub
    (Real.contDiff_exp.comp hv))).prodMk ((contDiff_snd.comp contDiff_fst).sub
      contDiff_snd))).mul ?_
  refine ContDiff.mul ?_ (Real.contDiff_exp.comp ?_)
  · exact (contDiff_const.mul hs).inv fun p => by have := hspos p; positivity
  · exact ContDiff.div (((contDiff_norm_sq ℝ).comp
      ((contDiff_snd.comp contDiff_fst).sub contDiff_snd)).neg) (contDiff_const.mul hs)
      fun p => by have := hspos p; positivity

lemma contDiff_plKer_snd (q : ℝ) (x : ℝ × ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (plKer q x) :=
  (contDiff_plKer q).comp (contDiff_const.prodMk contDiff_id)

lemma plKer_eq_zero_of_mem (q : ℝ) (x0 : ℝ × ℂ) (x : closedBall x0 1) (w : ℂ)
    (hw : w ∉ closedBall x0.2 (1 + Real.exp (|q| * (|x0.1| + 1)))) : plKer q x.1 w = 0 := by
  have hx := x.2
  rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hx
  have hv : |x.1.1| ≤ |x0.1| + 1 := by
    have := hx.1; rw [Real.dist_eq] at this
    calc |x.1.1| = |(x.1.1 - x0.1) + x0.1| := by ring_nf
      _ ≤ |x.1.1 - x0.1| + |x0.1| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hρ : plRad q (epsOf x.1.1) ≤ Real.exp (|q| * (|x0.1| + 1)) := by
    rw [plRad_epsOf]
    refine Real.exp_le_exp.2 ?_
    have h1 : q * x.1.1 ≤ |q| * |x.1.1| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |q| * |x.1.1| ≤ |q| * (|x0.1| + 1) := mul_le_mul_of_nonneg_left hv (abs_nonneg q)
    linarith [Real.exp_pos x.1.1]
  rw [← plTest_epsOf_apply]
  have hw' : w ∉ closedBall x.1.2 (plRad q (epsOf x.1.1)) := by
    rw [mem_closedBall, not_le] at hw ⊢
    linarith [dist_triangle w x.1.2 x0.2, hx.2]
  show plBump q _ _ (x.1.2 - w) * _ = 0
  rw [plBump_comp_eq_zero q _ _ _ hw', zero_mul]

 
def plTestV (q : ℝ) (x : ℝ × ℂ) : TestC := plTest q (epsOf x.1) (epsOf_mem x.1) x.2

 

theorem continuous_plTestV (q : ℝ) : Continuous (plTestV q) := by
  rw [continuous_iff_continuousAt]
  intro x0
  let K : TopologicalSpace.Compacts ℂ :=
    ⟨closedBall x0.2 (1 + Real.exp (|q| * (|x0.1| + 1))), isCompact_closedBall _ _⟩
  have hD : ∀ i : ℕ, Continuous fun p : closedBall x0 1 × ℂ =>
      iteratedFDeriv ℝ i (plKer q p.1.1) p.2 := by
    intro i
    have h1 := continuous_iteratedFDeriv_snd_rc (contDiff_plKer q) i
    have h2 : Continuous fun p : closedBall x0 1 × ℂ => ((p.1 : ℝ × ℂ), p.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact h1.comp h2
  have hc := continuous_testFamK K (fun x : closedBall x0 1 => plKer q x.1)
    (fun x => contDiff_plKer_snd q x.1) (plKer_eq_zero_of_mem q x0) hD
  have he : (fun x : closedBall x0 1 => plTestV q x.1) =
      (ofSuppC K) ∘ testFamK K (fun x : closedBall x0 1 => plKer q x.1)
        (fun x => contDiff_plKer_snd q x.1) (plKer_eq_zero_of_mem q x0) := by
    funext x; ext w; exact plTest_epsOf_apply q x.1 w
  have hB : Continuous fun x : closedBall x0 1 => plTestV q x.1 := by
    rw [he]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 hB).continuousAt
    (closedBall_mem_nhds x0 one_pos)

lemma plTest_congr (q : ℝ) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a = b) (z : ℂ) : plTest q a ha z = plTest q b hb z := by subst hab; rfl

def plTestT (q : ℝ) (p : ℝ × ℂ) : TestC :=
  if hp : p.1 ∈ Ioo (0 : ℝ) 1 then plTest q p.1 hp p.2 else 0

lemma plTestT_of_mem (q : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (z : ℂ) :
    plTestT q (ε, z) = plTest q ε hε z := by
  simp only [plTestT, hε, ↓reduceDIte]

theorem continuousOn_plTestT (q : ℝ) : ContinuousOn (plTestT q) (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  have h1 : ContinuousOn (fun p : ℝ × ℂ => (vOf p.1, p.2)) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    (continuousOn_vOf.comp continuous_fst.continuousOn fun p hp => (mem_prod.1 hp).1).prodMk
      continuous_snd.continuousOn
  refine ((continuous_plTestV q).comp_continuousOn h1).congr fun p hp => ?_
  have hp1 : p.1 ∈ Ioo (0 : ℝ) 1 := (mem_prod.1 hp).1
  simp only [Function.comp, plTestV, plTestT, hp1, ↓reduceDIte]
  exact plTest_congr q hp1 _ (epsOf_vOf hp1).symm p.2

 
def locTestT (p : ℝ × ℂ) : TestC := if hp : 0 < p.1 then locTest p.1 hp p.2 else 0

lemma locTestT_of_pos {ε : ℝ} (hε : 0 < ε) (z : ℂ) : locTestT (ε, z) = locTest ε hε z := by
  simp only [locTestT, hε, ↓reduceDIte]

theorem continuousOn_locTestT : ContinuousOn locTestT (Ioi (0 : ℝ) ×ˢ univ) := by
  have h1 : ContinuousOn (fun p : ℝ × ℂ => (Real.log p.1, p.2)) (Ioi 0 ×ˢ univ) :=
    ((Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
      (ne_of_gt (mem_prod.1 hp).1 : p.1 ≠ 0)).prodMk continuous_snd.continuousOn)
  refine (continuous_locTestE.comp_continuousOn h1).congr fun p hp => ?_
  have hp1 : 0 < p.1 := (mem_prod.1 hp).1
  simp only [Function.comp, locTestE, locTestT, hp1, ↓reduceDIte]
  exact locTest_congr hp1 (Real.exp_pos _) (Real.exp_log hp1).symm p.2

 

 

def plProf (q ε r : ℝ) : ℝ := locProf (Real.log (plRad q ε ^ 2)) (r : ℂ)

lemma plProf_eq (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : ℝ) :
    plProf q ε r = plBump q ε hε (r : ℂ) := (plBump_eq_locProf q ε hε _).symm

lemma continuousOn_plRad (q : ℝ) : ContinuousOn (plRad q) (Ioo (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun ε : ℝ => Real.log ε⁻¹) (Ioo (0 : ℝ) 1) :=
    Real.continuousOn_log.comp (continuousOn_inv₀.mono fun ε hε => (ne_of_gt hε.1))
      fun ε hε => inv_ne_zero (ne_of_gt hε.1)
  exact continuousOn_id.mul (h1.rpow_const fun ε hε => Or.inl (log_inv_pos hε).ne')

theorem continuousOn_plProf (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => plProf q p.1 p.2) (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  have hl : ContinuousOn (fun p : ℝ × ℝ => Real.log (plRad q p.1 ^ 2)) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    Real.continuousOn_log.comp (((continuousOn_plRad q).comp continuous_fst.continuousOn
      fun p hp => (mem_prod.1 hp).1).pow 2) fun p hp => (plRad_sq_pos q (mem_prod.1 hp).1).ne'
  exact contDiff_locProf.continuous.comp_continuousOn
    (hl.prodMk (Complex.continuous_ofReal.comp continuous_snd).continuousOn)

lemma plProf_mem_Icc (q ε r : ℝ) : plProf q ε r ∈ Icc (0 : ℝ) 1 := locProf_mem_Icc _ _

lemma continuousOn_dfgpsProf :
    ContinuousOn (fun p : ℝ × ℝ => locProf (Real.log p.1) (p.2 : ℂ)) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
  contDiff_locProf.continuous.comp_continuousOn
    ((Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
      (ne_of_gt (mem_prod.1 hp).1.1 : p.1 ≠ 0)).prodMk
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn)

 

 
def plZT (q ε : ℝ) : ℝ := ofCont (ContinuousMap.const ℂ 1) (plTestT q (ε, 0))

lemma plZT_of_mem (q : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : plZT q ε = plZ q ε hε := by
  rw [plZT, plTestT_of_mem q hε, ofCont_apply, plZ]
  simp

theorem continuousOn_plZT (q : ℝ) : ContinuousOn (plZT q) (Ioo (0 : ℝ) 1) :=
  (map_continuous (ofCont (ContinuousMap.const ℂ 1))).comp_continuousOn
    ((continuousOn_plTestT q).comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ hε => ⟨hε, mem_univ _⟩)

 

theorem plMollify_continuousOn (q : ℝ) (h : DistC) :
    ContinuousOn (fun p : ℝ × ℂ => if hp : p.1 ∈ Ioo (0 : ℝ) 1 then plMollify q p.1 hp h p.2 else 0)
      (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  have hZ : ContinuousOn (fun p : ℝ × ℂ => (plZT q p.1)⁻¹) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    ((continuousOn_plZT q).comp continuous_fst.continuousOn fun p hp => (mem_prod.1 hp).1).inv₀
      fun p hp => by
        show plZT q p.1 ≠ 0
        rw [plZT_of_mem q (mem_prod.1 hp).1]; exact (plZ_pos q _ _).ne'
  have hT : ContinuousOn (fun p : ℝ × ℂ => h (plTestT q p)) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    (map_continuous h).comp_continuousOn (continuousOn_plTestT q)
  refine (hZ.mul hT).congr fun p hp => ?_
  have hp1 : p.1 ∈ Ioo (0 : ℝ) 1 := (mem_prod.1 hp).1
  show (if hp : p.1 ∈ Ioo (0 : ℝ) 1 then plMollify q p.1 hp h p.2 else 0) =
    (plZT q p.1)⁻¹ * h (plTestT q p)
  simp only [hp1, ↓reduceDIte]
  rw [plZT_of_mem q hp1]
  obtain ⟨ε, z⟩ := p
  rw [plTestT_of_mem q hp1]; rfl

 
theorem continuous_plMollify (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (h : DistC) :
    Continuous (plMollify q ε hε h) := by
  have hc : ContinuousOn (fun z : ℂ => h (plTestT q (ε, z))) univ :=
    (map_continuous h).comp_continuousOn ((continuousOn_plTestT q).comp
      (continuous_const.prodMk continuous_id).continuousOn fun z _ => ⟨hε, mem_univ _⟩)
  have : plMollify q ε hε h = fun z => (plZ q ε hε)⁻¹ * h (plTestT q (ε, z)) := by
    funext z; rw [plTestT_of_mem q hε]; rfl
  rw [this]
  exact continuous_const.mul (continuousOn_univ.1 hc)

 
def plMollifyC (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (h : DistC) : C(ℂ, ℝ) :=
  ⟨plMollify q ε hε h, continuous_plMollify q ε hε h⟩

end SupercriticalLQGUniqueness.B2.Polylog
