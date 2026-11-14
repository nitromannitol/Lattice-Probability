/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P3PaidGeometry at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Costs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidChain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Sep

 




































set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open Uniqueness.BiLipschitz.PaidSeparators (sepAnn)
open Uniqueness.Toolkit.CompactPathInfimum (compactPathInf)

 

 




def GoodSiteIn (M₁ M₂ : LSCMetric) (K : ℝ) (x : ℂ) (r N : ℝ) (hr : 0 < r) : Prop :=
  0 < N ∧ ENNReal.ofReal N ≤ acrossIn M₁ x r (2 * r) ∧
    aroundDist M₂ (sepAnn x r hr) ≤ ENNReal.ofReal (K * N)

 




theorem acrossIn_le_len_of_crossing (M : LSCMetric) (x : ℂ) {r : ℝ} (hr : 0 < r)
    {P : ℝ → ℂ} {s t : ℝ} (hcurve : M.IsCurve P s t) (hPc : ContinuousOn P (Icc s t))
    (hstart : ‖P s - x‖ ≤ r) (hend : 2 * r ≤ ‖P t - x‖) :
    acrossIn M x r (2 * r) ≤ M.len P s t := by
  have hf : ContinuousOn (fun u => dist (P u) x) (Icc s t) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  obtain ⟨σ, τ, hsσ, hστ, hτt, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hcurve.1 hf (by linarith : r ≤ 2 * r)
      (by simpa only [dist_eq_norm] using hstart) (by simpa only [dist_eq_norm] using hend)
  have hsub : Icc σ τ ⊆ Icc s t := Icc_subset_Icc hsσ hτt
  have hc : M.IsCurve P σ τ := ⟨hστ, hcurve.2.mono hsub⟩
  have hin : ∀ u ∈ Icc σ τ, P u ∈ closedAnn x r (2 * r) := by
    intro u hu
    have h : dist (P u) x ∈ Icc r (2 * r) := hbetween u hu
    rw [dist_eq_norm] at h
    exact ⟨h.1, h.2⟩
  have hσS : P σ ∈ sphere x r := by rw [mem_sphere]; exact hσ
  have hτS : P τ ∈ sphere x (2 * r) := by rw [mem_sphere]; exact hτ
  calc acrossIn M x r (2 * r) ≤ M.len P σ τ := by
        unfold acrossIn compactPathInf
        exact iInf_le_of_le P (iInf_le_of_le σ (iInf_le_of_le τ (iInf_le_of_le hc
          (iInf_le_of_le hin (iInf_le_of_le hσS (iInf_le_of_le hτS le_rfl))))))
    _ ≤ M.len P s t := LQGMetric.MetricGeometry.curveLength_mono _ hsσ hτt

 




theorem exists_paid_separator_in (M₁ M₂ : LSCMetric) {K : ℝ} (hK : 0 < K) (x : ℂ) {r N : ℝ}
    (hr : 0 < r) (hgood : GoodSiteIn M₁ M₂ K x r N hr) :
    ∃ (Q : ℝ → ℂ) (a b : ℝ),
      M₂.IsCurve Q a b ∧
      (∀ t ∈ Icc a b, Q t ∈ (sepAnn x r hr).toSet) ∧
      M₂.len Q a b < ENNReal.ofReal (2 * K * N) ∧
      IsCompact (Q '' Icc a b) ∧ IsConnected (Q '' Icc a b) ∧
      closedBall x (2 * r) ⊆ connectedComponentIn (Q '' Icc a b)ᶜ x ∧
      connectedComponentIn (Q '' Icc a b)ᶜ x ⊆ ball x (3 * r) := by
  have hKN : 0 < K * N := mul_pos hK hgood.1
  have hstrict : ENNReal.ofReal (K * N) < ENNReal.ofReal (2 * K * N) := by
    apply ENNReal.ofReal_lt_ofReal_iff'.mpr
    constructor
    · nlinarith
    · nlinarith
  have hlt : aroundDist M₂ (sepAnn x r hr) < ENNReal.ofReal (2 * K * N) :=
    hgood.2.2.trans_lt hstrict
  dsimp only [aroundDist] at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
  obtain ⟨a, ha⟩ := iInf_lt_iff.mp hP
  obtain ⟨b, hb⟩ := iInf_lt_iff.mp ha
  obtain ⟨hcurve, hc⟩ := iInf_lt_iff.mp hb
  obtain ⟨hinside, hi⟩ := iInf_lt_iff.mp hc
  obtain ⟨hsep, hlen⟩ := iInf_lt_iff.mp hi
  have hAnn : P '' Icc a b ⊆ {w | 2 * r < dist w x ∧ dist w x < 3 * r} := by
    rintro y ⟨t, ht, rfl⟩
    exact Uniqueness.Toolkit.PlanarSeparation.candidate_annulus_subset_radii (sepAnn x r hr)
      (hinside t ht)
  have hball : P '' Icc a b ⊆ ball x (3 * r) := fun y hy => (hAnn hy).2
  have hPc : ContinuousOn P (Icc a b) :=
    Uniqueness.Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded M₂ P hcurve
      (isBounded_ball.subset hball)
  have hcompact : IsCompact (P '' Icc a b) := isCompact_Icc.image_of_continuousOn hPc
  have hconnected : IsConnected (P '' Icc a b) := (isConnected_Icc hcurve.1).image P hPc
  have hcert : LQGMetric.Disconnects (P '' Icc a b) (sphere x (2 * r)) (sphere x (3 * r)) :=
    Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  obtain ⟨hinner, houter⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.annular_component_bounds (by linarith : 0 < 2 * r)
      (by linarith : 2 * r < 3 * r) hcompact hAnn hcert
  exact ⟨P, a, b, hcurve, hinside, hlen, hcompact, hconnected, hinner, houter⟩

 



theorem paid_funded_in (M₁ M₂ : LSCMetric) {K : ℝ} (hK : 0 < K) (x : ℂ) {r N : ℝ}
    (hr : 0 < r) (hgood : GoodSiteIn M₁ M₂ K x r N hr) {P Q : ℝ → ℂ} {s t a b : ℝ}
    (hcurve : M₁.IsCurve P s t) (hPc : ContinuousOn P (Icc s t))
    (hstart : ‖P s - x‖ ≤ r) (hhit : P t ∈ Q '' Icc a b)
    (hQinside : ∀ u ∈ Icc a b, Q u ∈ (sepAnn x r hr).toSet)
    (hlen : M₂.len Q a b < ENNReal.ofReal (2 * K * N)) :
    M₂.len Q a b ≤ ENNReal.ofReal (2 * K) * M₁.len P s t := by
  have hhitRad : 2 * r ≤ ‖P t - x‖ := by
    obtain ⟨u, hu, hPu⟩ := hhit
    rw [← hPu]
    have hrad := Uniqueness.Toolkit.PlanarSeparation.candidate_annulus_subset_radii
      (sepAnn x r hr) (hQinside u hu)
    have hrad' : 2 * r < ‖Q u - x‖ := by
      simpa only [sepAnn, EuclideanAnnulus.innerRadius, EuclideanAnnulus.center,
        dist_eq_norm] using hrad.1
    exact hrad'.le
  have hN : ENNReal.ofReal N ≤ M₁.len P s t :=
    hgood.2.1.trans (acrossIn_le_len_of_crossing M₁ x hr hcurve hPc hstart hhitRad)
  calc M₂.len Q a b ≤ ENNReal.ofReal (2 * K * N) := hlen.le
    _ = ENNReal.ofReal (2 * K) * ENNReal.ofReal N := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * K)]
    _ ≤ ENNReal.ofReal (2 * K) * M₁.len P s t := by gcongr

 

 





theorem finite_stage_paid_recursion_in (M₁ M₂ : LSCMetric) {K : ℝ} (hK : 0 < K)
    {P : ℝ → ℂ} {T : ℝ} (hP : M₁.IsCurve P 0 T) (hPc : ContinuousOn P (Icc 0 T))
    (hfin : M₁.len P 0 T ≠ ∞) {ι : Type*} [Finite ι] (x : ι → ℂ) (r N : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hgood : ∀ i, GoodSiteIn M₁ M₂ K (x i) (r i) (N i) (hr i))
    (hcover : ∀ s ∈ Icc (0 : ℝ) T, ∃ i, dist (P s) (x i) < r i / 2) :
    ∃ (Q : ι → ℝ → ℂ) (a b : ι → ℝ) (I : ℝ → ι) (J : ℕ) (S : ℕ → ℝ),
      (∀ i,
        M₂.IsCurve (Q i) (a i) (b i) ∧
        (∀ t ∈ Icc (a i) (b i), Q i t ∈ (sepAnn (x i) (r i) (hr i)).toSet) ∧
        M₂.len (Q i) (a i) (b i) < ENNReal.ofReal (2 * K * N i) ∧
        IsCompact (Q i '' Icc (a i) (b i)) ∧
        IsConnected (Q i '' Icc (a i) (b i)) ∧
        closedBall (x i) (2 * r i) ⊆ connectedComponentIn (Q i '' Icc (a i) (b i))ᶜ (x i) ∧
        connectedComponentIn (Q i '' Icc (a i) (b i))ᶜ (x i) ⊆ ball (x i) (3 * r i)) ∧
      (∀ s ∈ Icc (0 : ℝ) T, dist (P s) (x (I s)) < r (I s) / 2) ∧
      S 0 = 0 ∧ Monotone S ∧ (∀ n, S n ∈ Icc (0 : ℝ) T) ∧
      (∀ j < J, S j < S (j + 1) ∧
        P (S (j + 1)) ∈ Q (I (S j)) '' Icc (a (I (S j))) (b (I (S j))) ∧
        ∀ u ∈ Ico (S j) (S (j + 1)),
          P u ∈ connectedComponentIn
            (Q (I (S j)) '' Icc (a (I (S j))) (b (I (S j))))ᶜ (x (I (S j)))) ∧
      (∀ u ∈ Icc (S J) T,
        P u ∈ connectedComponentIn
          (Q (I (S J)) '' Icc (a (I (S J))) (b (I (S J))))ᶜ (x (I (S J)))) := by
  classical
  have hex := fun i => exists_paid_separator_in M₁ M₂ hK (x i) (hr i) (hgood i)
  choose Q a b hdata using hex
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hP.1⟩
  obtain ⟨i₀, -⟩ := hcover 0 hI0
  have : Nonempty ι := ⟨i₀⟩
  choose! I hinner using hcover
  obtain ⟨imin, hmin⟩ := Finite.exists_min N
  let Kt : ι → Set ℂ := fun i => Q i '' Icc (a i) (b i)
  have hK' : ∀ i, IsClosed (Kt i) := fun i => (hdata i).2.2.2.1.isClosed
  have hstart : ∀ s ∈ Icc (0 : ℝ) T, P s ∈ connectedComponentIn (Kt (I s))ᶜ (x (I s)) := by
    intro s hs
    have hrad : dist (P s) (x (I s)) ≤ 2 * r (I s) := by
      linarith [hinner s hs, hr (I s)]
    exact (hdata (I s)).2.2.2.2.2.1 (by simpa only [mem_closedBall] using hrad)
  have hcost : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc s T,
      P t ∈ Kt (I s) → ENNReal.ofReal (N imin) ≤ M₁.len P s t := by
    intro s hs t ht htK
    have hsub : Icc s t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs.1 ht.2
    have hcurve : M₁.IsCurve P s t := ⟨ht.1, hP.2.mono hsub⟩
    have hstartRad : ‖P s - x (I s)‖ ≤ r (I s) := by
      rw [← dist_eq_norm]
      linarith [hinner s hs, hr (I s)]
    obtain ⟨u, hu, hPu⟩ := htK
    have hrad := Uniqueness.Toolkit.PlanarSeparation.candidate_annulus_subset_radii
      (sepAnn (x (I s)) (r (I s)) (hr (I s))) ((hdata (I s)).2.1 u hu)
    have hendRad : 2 * r (I s) ≤ ‖P t - x (I s)‖ := by
      rw [← hPu]
      have hrad' : 2 * r (I s) < ‖Q (I s) u - x (I s)‖ := by
        simpa only [sepAnn, EuclideanAnnulus.innerRadius, EuclideanAnnulus.center,
          dist_eq_norm] using hrad.1
      exact hrad'.le
    calc ENNReal.ofReal (N imin) ≤ ENNReal.ofReal (N (I s)) := ENNReal.ofReal_le_ofReal (hmin _)
      _ ≤ acrossIn M₁ (x (I s)) (r (I s)) (2 * r (I s)) := (hgood (I s)).2.1
      _ ≤ M₁.len P s t :=
        acrossIn_le_len_of_crossing M₁ (x (I s)) (hr (I s)) hcurve (hPc.mono hsub) hstartRad
          hendRad
  obtain ⟨J, S, hS0, hSmono, hSI, hpaid, hterminal⟩ :=
    Uniqueness.BiLipschitz.PaidSeparators.finite_first_hit_recursion M₁ hP hPc hfin
      (hgood imin).1 Kt x I hK' hstart hcost
  exact ⟨Q, a, b, I, J, S, hdata, hinner, hS0, hSmono, hSI, hpaid, hterminal⟩

 

 



theorem internal_chain_core {κ : Type*} (M : LSCMetric) (Y : Set ℂ) (K : κ → Set ℂ)
    (L : κ → ℝ≥0∞) (hKY : ∀ i, K i ⊆ Y)
    (hcost : ∀ i x y (hx : x ∈ K i) (hy : y ∈ K i),
      M.internal Y (⟨x, hKY i hx⟩, ⟨y, hKY i hy⟩) ≤ L i)
    (i : κ) (l : List κ) (j : κ)
    (hchain : (i :: l).IsChain fun u v => (K u ∩ K v).Nonempty)
    (hlast : (i :: l).getLast (List.cons_ne_nil i l) = j)
    {x y : ℂ} (hx : x ∈ K i) (hy : y ∈ K j) :
    M.internal Y (⟨x, hKY i hx⟩, ⟨y, hKY j hy⟩) ≤ ((i :: l).map L).sum := by
  induction l generalizing i x with
  | nil =>
      have hij : i = j := by simpa using hlast
      subst j
      simpa using hcost i x y hx hy
  | cons k tail ih =>
      have hik : (K i ∩ K k).Nonempty := (List.isChain_cons_cons.mp hchain).1
      obtain ⟨z, hzi, hzk⟩ := hik
      have htail : (k :: tail).IsChain fun u v => (K u ∩ K v).Nonempty :=
        (List.isChain_cons_cons.mp hchain).2
      have hlast' : (k :: tail).getLast (List.cons_ne_nil k tail) = j := by
        simpa using hlast
      calc M.internal Y (⟨x, hKY i hx⟩, ⟨y, hKY j hy⟩)
          ≤ M.internal Y (⟨x, hKY i hx⟩, ⟨z, hKY i hzi⟩) +
              M.internal Y (⟨z, hKY k hzk⟩, ⟨y, hKY j hy⟩) :=
            (LSCMetric.isExtMetric_internal M Y).2.2.2 _ _ _
        _ ≤ L i + ((k :: tail).map L).sum :=
            add_le_add (hcost i x z hx hzi) (ih k htail hlast' hzk)
        _ = ((i :: k :: tail).map L).sum := by simp only [List.map_cons, List.sum_cons]

 




theorem paidTrace_internal_chain {ι : Type*} [DecidableEq ι] (M : LSCMetric) (Y : Set ℂ)
    (S₀ : Finset ι) (K : ι → Set ℂ) (P : ι → ℝ → ℂ) (a b : ι → ℝ) (c : ι → ℂ) (A : Set ℂ)
    (hAne : A.Nonempty) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S₀, connectedComponentIn (K i)ᶜ (c i))
    (hcurve : ∀ i ∈ S₀, M.IsCurve (P i) (a i) (b i))
    (hEucl : ∀ i ∈ S₀, ContinuousOn (P i) (Icc (a i) (b i)))
    (htrace : ∀ i ∈ S₀, K i = P i '' Icc (a i) (b i))
    (hKY : ∀ i ∈ S₀, K i ⊆ Y)
    (hbounded : ∀ i ∈ S₀, Bornology.IsBounded (connectedComponentIn (K i)ᶜ (c i))) :
    ∃ S ⊆ S₀,
      A ⊆ (⋃ i ∈ S, connectedComponentIn (K i)ᶜ (c i)) ∧
      ∀ i ∈ S, ∀ j ∈ S, ∀ x y : ℂ, ∀ (hx : x ∈ Y) (hy : y ∈ Y), x ∈ K i → y ∈ K j →
        M.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ ∑ k ∈ S, M.len (P k) (a k) (b k) := by
  classical
  have hc : ∀ i ∈ S₀, IsCompact (K i) := by
    intro i hi
    rw [htrace i hi]
    exact isCompact_Icc.image_of_continuousOn (hEucl i hi)
  have hconn : ∀ i ∈ S₀, IsConnected (K i) := by
    intro i hi
    rw [htrace i hi]
    exact (isConnected_Icc (hcurve i hi).1).image (P i) (hEucl i hi)
  obtain ⟨S, hSS₀, hSA, _, _, hchains⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.finiteObstacle_chain S₀ K c A hAne hA hcov hc hconn
      hbounded
  refine ⟨S, hSS₀, hSA, ?_⟩
  intro i hi j hj x y hxY hyY hx hy
  obtain ⟨l, hne, hfirst, hlast, hnodup, hchain⟩ := hchains ⟨i, hi⟩ ⟨j, hj⟩
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons u tail =>
      have hui : u = ⟨i, hi⟩ := by simpa using hfirst
      subst hui
      have hlast' : (⟨i, hi⟩ :: tail).getLast (List.cons_ne_nil _ tail) = ⟨j, hj⟩ := by
        simpa using hlast
      have hKY' : ∀ q : {t // t ∈ S}, K q.val ⊆ Y := fun q => hKY q.val (hSS₀ q.property)
      have hcost : ∀ (q : {t // t ∈ S}) (v w : ℂ) (hv : v ∈ K q.val) (hw : w ∈ K q.val),
          M.internal Y (⟨v, hKY' q hv⟩, ⟨w, hKY' q hw⟩) ≤
            M.len (P q.val) (a q.val) (b q.val) := by
        intro q v w hv hw
        have hq : q.val ∈ S₀ := hSS₀ q.property
        have hv' := hv
        have hw' := hw
        rw [htrace q.val hq] at hv' hw'
        obtain ⟨p, hp, hpv⟩ := hv'
        obtain ⟨p', hp', hpw⟩ := hw'
        subst hpv hpw
        exact Uniqueness.Objects.Excursions.internal_le_len_of_mem M (hcurve q.val hq)
          (fun t ht => hKY q.val hq (by rw [htrace q.val hq]; exact ⟨t, ht, rfl⟩)) hp hp' _ _
      have hpaid := internal_chain_core M Y (fun q : {t // t ∈ S} => K q.val)
        (fun q => M.len (P q.val) (a q.val) (b q.val)) hKY' hcost ⟨i, hi⟩ tail ⟨j, hj⟩ hchain
        hlast' hx hy
      have hsub : (⟨i, hi⟩ :: tail).toFinset ⊆ S.attach := fun q _ => Finset.mem_attach S q
      have hsum : ((⟨i, hi⟩ :: tail).map (fun q : {t // t ∈ S} =>
          M.len (P q.val) (a q.val) (b q.val))).sum ≤ ∑ k ∈ S, M.len (P k) (a k) (b k) := by
        rw [← List.sum_toFinset _ hnodup]
        calc _ ≤ ∑ q ∈ S.attach, M.len (P q.val) (a q.val) (b q.val) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (by simp)
          _ = ∑ k ∈ S, M.len (P k) (a k) (b k) :=
              Finset.sum_attach S (fun k => M.len (P k) (a k) (b k))
      exact hpaid.trans hsum

 


theorem paid_prefix_internal_chain (M₂ : LSCMetric) (Y : Set ℂ) {P : ℝ → ℂ} {T : ℝ}
    (hPc : ContinuousOn P (Icc 0 T)) (J : ℕ) (hJ : 0 < J) (S : ℕ → ℝ)
    (hS0 : S 0 = 0) (hSmono : Monotone S) (hSI : ∀ n, S n ∈ Icc (0 : ℝ) T)
    (K : ℕ → Set ℂ) (c : ℕ → ℂ) (Q : ℕ → ℝ → ℂ) (a b : ℕ → ℝ)
    (hcurve : ∀ j < J, M₂.IsCurve (Q j) (a j) (b j))
    (htrace : ∀ j < J, K j = Q j '' Icc (a j) (b j))
    (hcompact : ∀ j < J, IsCompact (K j))
    (hKY : ∀ j < J, K j ⊆ Y)
    (hbounded : ∀ j < J, Bornology.IsBounded (connectedComponentIn (K j)ᶜ (c j)))
    (hpaidStrict : ∀ j < J, S j < S (j + 1))
    (hpaid : ∀ j < J, ∀ u ∈ Ico (S j) (S (j + 1)), P u ∈ connectedComponentIn (K j)ᶜ (c j)) :
    ∃ F ⊆ Finset.range J,
      P '' Ico 0 (S J) ⊆ ⋃ j ∈ F, connectedComponentIn (K j)ᶜ (c j) ∧
      ∀ i ∈ F, ∀ j ∈ F, ∀ x y : ℂ, ∀ (hx : x ∈ Y) (hy : y ∈ Y), x ∈ K i → y ∈ K j →
        M₂.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ ∑ q ∈ F, M₂.len (Q q) (a q) (b q) := by
  classical
  have hSJpos : 0 < S J := by
    have h01 : 0 < S 1 := hS0 ▸ hpaidStrict 0 hJ
    exact h01.trans_le (hSmono (by omega : 1 ≤ J))
  let A : Set ℂ := P '' Ico 0 (S J)
  have hAne : A.Nonempty := ⟨P 0, 0, ⟨le_rfl, hSJpos⟩, rfl⟩
  have hApc : IsPreconnected A :=
    isPreconnected_Ico.image P (hPc.mono (Ico_subset_Icc_self.trans
      (Icc_subset_Icc le_rfl (hSI J).2)))
  have hcov : A ⊆ ⋃ j ∈ Finset.range J, connectedComponentIn (K j)ᶜ (c j) := by
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨j, hj, huj⟩ :=
      Uniqueness.BiLipschitz.PaidSeparators.mem_paid_interval_of_mem_prefix S hSmono hS0 J hu
    exact mem_biUnion (Finset.mem_range.mpr hj) (hpaid j hj u huj)
  have hEucl : ∀ j ∈ Finset.range J, ContinuousOn (Q j) (Icc (a j) (b j)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hc : IsCompact (Q j '' Icc (a j) (b j)) := by
      rw [← htrace j hj']
      exact hcompact j hj'
    exact Uniqueness.Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded M₂
      (Q j) (hcurve j hj') hc.isBounded
  exact paidTrace_internal_chain M₂ Y (Finset.range J) K Q a b c A hAne hApc hcov
    (fun j hj => hcurve j (Finset.mem_range.mp hj)) hEucl
    (fun j hj => htrace j (Finset.mem_range.mp hj))
    (fun j hj => hKY j (Finset.mem_range.mp hj))
    (fun j hj => hbounded j (Finset.mem_range.mp hj))

 


theorem selected_paid_sum_le_in (M₁ M₂ : LSCMetric) {P : ℝ → ℂ} {T : ℝ} (κ : ℝ≥0∞)
    (J : ℕ) (S : ℕ → ℝ) (hS0 : S 0 = 0) (hSmono : Monotone S) (hSJ : S J ≤ T)
    (F : Finset ℕ) (hF : F ⊆ Finset.range J) (Q : ℕ → ℝ → ℂ) (a b : ℕ → ℝ)
    (hfund : ∀ j < J, M₂.len (Q j) (a j) (b j) ≤ κ * M₁.len P (S j) (S (j + 1))) :
    (∑ j ∈ F, M₂.len (Q j) (a j) (b j)) ≤ κ * M₁.len P 0 T := by
  calc (∑ j ∈ F, M₂.len (Q j) (a j) (b j))
      ≤ ∑ j ∈ Finset.range J, M₂.len (Q j) (a j) (b j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hF (by simp)
    _ ≤ ∑ j ∈ Finset.range J, κ * M₁.len P (S j) (S (j + 1)) :=
        Finset.sum_le_sum fun j hj => hfund j (Finset.mem_range.mp hj)
    _ = κ * ∑ j ∈ Finset.range J, M₁.len P (S j) (S (j + 1)) := by rw [Finset.mul_sum]
    _ = κ * M₁.len P 0 (S J) := by
        rw [← hS0]
        exact congrArg (fun v : ℝ≥0∞ => κ * v)
          (LQGMetric.MetricGeometry.sum_curveLength_eq (M₁.pt ∘ P) hSmono J)
    _ ≤ κ * M₁.len P 0 T := by
        gcongr
        exact LQGMetric.MetricGeometry.curveLength_mono (M₁.pt ∘ P) (hS0 ▸ le_rfl) hSJ

 

 





theorem finite_stage_internal_bound (M₁ M₂ : LSCMetric) {K ρ : ℝ} (hK : 0 < K) (hρ : 0 < ρ)
    {U : Set ℂ} {P : ℝ → ℂ} {T : ℝ} (hP : M₁.IsCurve P 0 T) (hPc : ContinuousOn P (Icc 0 T))
    (hPU : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ U) (hfin : M₁.len P 0 T ≠ ∞)
    {ι : Type*} [Finite ι] (x : ι → ℂ) (r N : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hrρ : ∀ i, 20 * r i ≤ ρ) (hgood : ∀ i, GoodSiteIn M₁ M₂ K (x i) (r i) (N i) (hr i))
    (hcover : ∀ s ∈ Icc (0 : ℝ) T, ∃ i, dist (P s) (x i) < r i / 2) :
    M₂.internalSetDist (thickening ρ U) {y | (y : ℂ) ∈ ball (P 0) ρ}
        {y | (y : ℂ) ∈ ball (P T) ρ} ≤ ENNReal.ofReal (2 * K) * M₁.len P 0 T := by
  classical
  set ε : ℝ := ρ / 20 with hεdef
  have hrε : ∀ i, r i ≤ ε := fun i => by rw [hεdef]; linarith [hrρ i]
  set Y : Set ℂ := thickening ρ U with hYdef
  have hUY : U ⊆ Y := self_subset_thickening hρ U
  have hP0Y : P 0 ∈ Y := hUY (hPU 0 (left_mem_Icc.2 hP.1))
  have hreduce : ∀ (z' w' : ℂ) (hz' : z' ∈ Y) (hw' : w' ∈ Y), dist z' (P 0) < ρ →
      dist w' (P T) < ρ →
      M₂.internalSetDist Y {y | (y : ℂ) ∈ ball (P 0) ρ} {y | (y : ℂ) ∈ ball (P T) ρ} ≤
        M₂.internal Y (⟨z', hz'⟩, ⟨w', hw'⟩) := by
    intro z' w' hz' hw' hz'0 hw'T
    have h1 : (⟨z', hz'⟩ : Y) ∈ {y : Y | (y : ℂ) ∈ ball (P 0) ρ} := by
      show z' ∈ ball (P 0) ρ
      exact mem_ball.2 hz'0
    have h2 : (⟨w', hw'⟩ : Y) ∈ {y : Y | (y : ℂ) ∈ ball (P T) ρ} := by
      show w' ∈ ball (P T) ρ
      exact mem_ball.2 hw'T
    unfold LSCMetric.internalSetDist
    exact iInf₂_le_of_le _ h1 (iInf₂_le _ h2)
  by_cases hclose : dist (P 0) (P T) ≤ 6 * ε
  · have h0 := hreduce (P 0) (P 0) hP0Y hP0Y (by simpa only [dist_self] using hρ)
      (by linarith [hεdef])
    rw [(LSCMetric.isExtMetric_internal M₂ Y).1] at h0
    exact h0.trans bot_le
  push Not at hclose
  obtain ⟨Q, a, b, I, J, S, hdata, hinner, hS0, hSmono, hSI, hpaid, hterminal⟩ :=
    finite_stage_paid_recursion_in M₁ M₂ hK hP hPc hfin x r N hr hgood hcover
  let Kt : ℕ → Set ℂ := fun j => Q (I (S j)) '' Icc (a (I (S j))) (b (I (S j)))
  let c : ℕ → ℂ := fun j => x (I (S j))
  let V : ℕ → Set ℂ := fun j => connectedComponentIn (Kt j)ᶜ (c j)
  have hVouter : ∀ j, V j ⊆ ball (c j) (3 * r (I (S j))) :=
    fun j => (hdata (I (S j))).2.2.2.2.2.2
  have hJpos : 0 < J := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · have hzV : P 0 ∈ V 0 := by
        have h := hterminal 0 (by rw [hJ0, hS0]; exact left_mem_Icc.2 hP.1)
        simpa [V, Kt, c, hJ0] using h
      have hwV : P T ∈ V 0 := by
        have h := hterminal T (by rw [hJ0, hS0]; exact right_mem_Icc.2 hP.1)
        simpa [V, Kt, c, hJ0] using h
      have hclose' :=
        Uniqueness.BiLipschitz.PaidSeparators.component_pair_close (hr (I (S 0)))
          (hrε (I (S 0))) (hVouter 0) hzV hwV
      exact False.elim ((not_lt_of_ge hclose.le) hclose')
    · exact hJ0
  have hSJpos : 0 < S J := by
    have h01 : 0 < S 1 := hS0 ▸ (hpaid 0 hJpos).1
    exact h01.trans_le (hSmono (by omega : 1 ≤ J))
  have hKball : ∀ j, Kt j ⊆ ball (c j) (3 * r (I (S j))) := by
    intro j y hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact (Uniqueness.Toolkit.PlanarSeparation.candidate_annulus_subset_radii
      (sepAnn (x (I (S j))) (r (I (S j))) (hr (I (S j)))) ((hdata (I (S j))).2.1 u hu)).2
  have hKY : ∀ j, Kt j ⊆ Y := by
    intro j y hy
    have h1 : dist y (c j) < 3 * r (I (S j)) := hKball j hy
    have h2 : dist (P (S j)) (c j) < r (I (S j)) / 2 := hinner (S j) (hSI j)
    have h3 : dist y (P (S j)) < ρ := by
      calc dist y (P (S j)) ≤ dist y (c j) + dist (c j) (P (S j)) := dist_triangle _ _ _
        _ < 3 * r (I (S j)) + r (I (S j)) / 2 := by rw [dist_comm (c j)]; exact add_lt_add h1 h2
        _ ≤ ρ := by linarith [hrρ (I (S j)), hr (I (S j))]
    exact mem_thickening_iff.2 ⟨P (S j), hPU _ (hSI j), h3⟩
  obtain ⟨F, hF, hcovF, hchain⟩ :=
    paid_prefix_internal_chain M₂ Y hPc J hJpos S hS0 hSmono hSI Kt c
      (fun j => Q (I (S j))) (fun j => a (I (S j))) (fun j => b (I (S j)))
      (fun j _ => (hdata (I (S j))).1) (fun j _ => rfl)
      (fun j _ => (hdata (I (S j))).2.2.2.1) (fun j _ => hKY j)
      (fun j _ => isBounded_ball.subset (hVouter j))
      (fun j hj => (hpaid j hj).1) (fun j hj u hu => (hpaid j hj).2.2 u hu)
  have hzA : P 0 ∈ P '' Ico 0 (S J) := ⟨0, ⟨le_rfl, hSJpos⟩, rfl⟩
  obtain ⟨js, hjsF, hzV⟩ := mem_iUnion₂.mp (hcovF hzA)
  obtain ⟨je, hjeF, hpVcl⟩ :=
    Uniqueness.BiLipschitz.PaidSeparators.exists_selected_component_at_terminal F V hSJpos
      (hSI J).2 hPc hcovF
  have hKne : ∀ j, (Kt j).Nonempty := fun j =>
    ⟨Q (I (S j)) (a (I (S j))), a (I (S j)), left_mem_Icc.2 (hdata (I (S j))).1.1, rfl⟩
  obtain ⟨z', hz'K, hz'near⟩ :=
    Uniqueness.BiLipschitz.PaidSeparators.exists_trace_near_component (hr (I (S js)))
      (hrε (I (S js))) (hKne js) (hKball js) (hVouter js) (subset_closure hzV)
  have hpLast : P (S J) ∈ V J := hterminal (S J) (left_mem_Icc.2 (hSI J).2)
  have hwLast : P T ∈ V J := hterminal T (right_mem_Icc.2 (hSI J).2)
  obtain ⟨w', hw'K, hw'near⟩ :=
    Uniqueness.BiLipschitz.PaidSeparators.exists_trace_near_terminal
      (hr (I (S je))) (hr (I (S J))) (hrε (I (S je))) (hrε (I (S J)))
      (hKne je) (hKball je) (hVouter je) hpVcl (hVouter J) hpLast hwLast
  have hfund : ∀ j < J, M₂.len (Q (I (S j))) (a (I (S j))) (b (I (S j))) ≤
      ENNReal.ofReal (2 * K) * M₁.len P (S j) (S (j + 1)) := by
    intro j hj
    have hjpaid := hpaid j hj
    have hsub : Icc (S j) (S (j + 1)) ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc (hSI j).1 (hSI (j + 1)).2
    have hcurve : M₁.IsCurve P (S j) (S (j + 1)) := ⟨hjpaid.1.le, hP.2.mono hsub⟩
    have hstartRad : ‖P (S j) - x (I (S j))‖ ≤ r (I (S j)) := by
      rw [← dist_eq_norm]
      linarith [hinner (S j) (hSI j), hr (I (S j))]
    exact paid_funded_in M₁ M₂ hK (x (I (S j))) (hr (I (S j))) (hgood (I (S j))) hcurve
      (hPc.mono hsub) hstartRad hjpaid.2.1 (hdata (I (S j))).2.1 (hdata (I (S j))).2.2.1
  have hsum := selected_paid_sum_le_in M₁ M₂ (ENNReal.ofReal (2 * K)) J S hS0 hSmono (hSI J).2
    F hF (fun j => Q (I (S j))) (fun j => a (I (S j))) (fun j => b (I (S j))) hfund
  have hz'Y := hKY js hz'K
  have hw'Y := hKY je hw'K
  calc M₂.internalSetDist Y {y | (y : ℂ) ∈ ball (P 0) ρ} {y | (y : ℂ) ∈ ball (P T) ρ}
      ≤ M₂.internal Y (⟨z', hz'Y⟩, ⟨w', hw'Y⟩) :=
        hreduce z' w' hz'Y hw'Y (by rw [dist_comm]; linarith [hεdef])
          (by rw [dist_comm]; linarith [hεdef])
    _ ≤ _ := hchain js hjsF je hjeF z' w' hz'Y hw'Y hz'K hw'K
    _ ≤ _ := hsum

 
lemma len_comp_add (M : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) :
    M.len (fun t => P (t + a)) 0 (b - a) = M.len P a b := by
  unfold LSCMetric.len
  have hcomp : (M.pt ∘ fun t => P (t + a)) = (M.pt ∘ P) ∘ fun t => t + a := rfl
  rw [hcomp, eVariationOn.comp_eq_of_monotoneOn _ _ (fun u _ v _ huv => by linarith),
    image_add_const_Icc, zero_add, sub_add_cancel]

 





theorem internalSetDist_le_of_goodSites (M₁ M₂ : LSCMetric) {K ρ : ℝ} (hK : 0 < K) (hρ : 0 < ρ)
    {U : Set ℂ} (hU : Bornology.IsBounded U) {ι : Type*} [Finite ι] (x : ι → ℂ) (r N : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hrρ : ∀ i, 20 * r i ≤ ρ)
    (hgood : ∀ i, GoodSiteIn M₁ M₂ K (x i) (r i) (N i) (hr i))
    (hcover : ∀ y ∈ U, ∃ i, dist y (x i) < r i / 2) (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) :
    M₂.internalSetDist (thickening ρ U) {y | (y : ℂ) ∈ ball z ρ} {y | (y : ℂ) ∈ ball w ρ} ≤
      ENNReal.ofReal (2 * K) * M₁.internal U (⟨z, hz⟩, ⟨w, hw⟩) := by
  have hc0 : ENNReal.ofReal (2 * K) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hcT : ENNReal.ofReal (2 * K) ≠ ∞ := ENNReal.ofReal_ne_top
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne hc0 hcT]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPU => le_iInf fun ha => le_iInf fun hb => ?_
  by_cases hfin : M₁.len P a b = ∞
  · rw [hfin, ENNReal.mul_top hc0]
    exact le_top
  have hab := hP.1
  have hP' : M₁.IsCurve (fun t => P (t + a)) 0 (b - a) := by
    refine ⟨by linarith, ?_⟩
    have hmaps : MapsTo (fun t : ℝ => t + a) (Icc 0 (b - a)) (Icc a b) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hP.2.comp (continuousOn_id.add continuousOn_const) hmaps
  have hP'U : ∀ t ∈ Icc (0 : ℝ) (b - a), P (t + a) ∈ U := fun t ht =>
    hPU (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hP'c : ContinuousOn (fun t => P (t + a)) (Icc 0 (b - a)) :=
    Uniqueness.Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded M₁ _ hP'
      (hU.subset (image_subset_iff.2 hP'U))
  have hlen := len_comp_add M₁ P a b
  have h := finite_stage_internal_bound M₁ M₂ hK hρ hP' hP'c hP'U (by rwa [hlen]) x r N hr hrρ
    hgood (fun s hs => hcover _ (hP'U s hs))
  have h0 : P (0 + a) = z := by rw [zero_add]; exact ha
  have hT : P (b - a + a) = w := by rw [sub_add_cancel]; exact hb
  simp only [h0, hT, hlen] at h
  exact h

end SupercriticalLQGUniqueness.B2.Polylog
