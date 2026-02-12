import LeanSlt.NNGPResNet.GaussianLinearForms
import LeanSlt.NNGPResNet.Scalar
import SLT.Dudley
import SLT.CoveringNumber
import SLT.LeastSquares.LinearRegression.EntropyIntegral

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet

noncomputable section

def sphereSet (m : Nat) : Set (EuclideanSpace Real (Fin m)) :=
  Metric.sphere (0 : EuclideanSpace Real (Fin m)) 1

abbrev SphereSetSub (m : Nat) :=
  {t : EuclideanSpace Real (Fin m) // t ∈ sphereSet m}

def sphereToSphereSetSub (m : Nat) (u : Sphere m) : SphereSetSub m :=
  ⟨u.1, by
    unfold sphereSet
    simpa [dist_eq_norm] using u.2⟩

def sphereSetSubToSphere (m : Nat) (t : SphereSetSub m) : Sphere m :=
  ⟨t.1, by
    have ht : t.1 ∈ sphereSet m := t.2
    unfold sphereSet at ht
    rw [Metric.mem_sphere] at ht
    rw [dist_eq_norm] at ht
    simpa using ht⟩

def sphereEquivSphereSetSub (m : Nat) : Sphere m ≃ SphereSetSub m where
  toFun := sphereToSphereSetSub m
  invFun := sphereSetSubToSphere m
  left_inv := by
    intro u
    cases u
    rfl
  right_inv := by
    intro t
    cases t
    rfl

def sphereBaseVec (m : Nat) (hm : 0 < m) : EuclideanSpace Real (Fin m) :=
  EuclideanSpace.single (Fin.mk 0 hm) (1 : Real)

lemma norm_sphereBaseVec (m : Nat) (hm : 0 < m) :
    norm (sphereBaseVec m hm) = 1 := by
  unfold sphereBaseVec
  simp [EuclideanSpace.norm_single]

def sphereBasePoint (m : Nat) (hm : 0 < m) : Sphere m :=
  ⟨sphereBaseVec m hm, norm_sphereBaseVec m hm⟩

lemma sphereBaseVec_mem_sphereSet (m : Nat) (hm : 0 < m) :
    sphereBaseVec m hm ∈ sphereSet m := by
  unfold sphereSet
  simp [norm_sphereBaseVec m hm]

def centeredAmbientProcess {m L rm : Nat} (hm : 0 < m)
    (u : EuclideanSpace Real (Fin m)) (omega : OmegaNN L m rm) : Real :=
  M_u (L := L) (m := m) (rm := rm) u omega -
    M_u (L := L) (m := m) (rm := rm) (sphereBaseVec m hm) omega

lemma dist_sphere_eq_norm {m : Nat} (u v : Sphere m) :
    dist u v = norm (u.1 - v.1) := by
  change dist u.1 v.1 = norm (u.1 - v.1)
  simp [dist_eq_norm]

theorem map_X_diff_gaussian
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (u v : Sphere m) :
    (muNN L m rm).map (fun omega => X (L := L) (m := m) (rm := rm) u omega -
      X (L := L) (m := m) (rm := rm) v omega) =
      gaussianReal 0 (vecVarNN L (u.1 - v.1)) := by
  have hSub := M_u_sub (L := L) (m := m) (rm := rm) (u := u.1) (v := v.1)
  have hEq :
      (fun omega => X (L := L) (m := m) (rm := rm) u omega -
        X (L := L) (m := m) (rm := rm) v omega) =
      M_u (L := L) (m := m) (rm := rm) (u.1 - v.1) := by
    funext omega
    have hu : M_u (L := L) (m := m) (rm := rm) u.1 omega =
        X (L := L) (m := m) (rm := rm) u omega := by
      simpa using congrArg (fun f => f omega) (M_u_eq_X (L := L) (m := m) (rm := rm) u)
    have hv : M_u (L := L) (m := m) (rm := rm) v.1 omega =
        X (L := L) (m := m) (rm := rm) v omega := by
      simpa using congrArg (fun f => f omega) (M_u_eq_X (L := L) (m := m) (rm := rm) v)
    have hs := congrArg (fun f => f omega) hSub
    calc
      X (L := L) (m := m) (rm := rm) u omega - X (L := L) (m := m) (rm := rm) v omega
          = M_u (L := L) (m := m) (rm := rm) u.1 omega -
              M_u (L := L) (m := m) (rm := rm) v.1 omega := by
                rw [hu, hv]
      _ = M_u (L := L) (m := m) (rm := rm) (u.1 - v.1) omega := by
            simpa using hs
  simpa [hEq] using map_M_u_gaussian_any (m := m) (L := L) (rm := rm) hL hrm (u.1 - v.1)

theorem sphere_process_isSubGaussian
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm) :
    IsSubGaussianProcess
      (muNN L m rm)
      (X (L := L) (m := m) (rm := rm))
      (1 / (L : Real)) := by
  intro u v l
  have hMap := map_X_diff_gaussian (m := m) (L := L) (rm := rm) hL hrm u v
  have hmgf := mgf_gaussianReal
    (p := muNN L m rm)
    (X := fun omega => X (L := L) (m := m) (rm := rm) u omega -
      X (L := L) (m := m) (rm := rm) v omega)
    (μ := (0 : Real))
    (v := vecVarNN L (u.1 - v.1))
    hMap l
  have hdist : dist u v = norm (u.1 - v.1) := dist_sphere_eq_norm (u := u) (v := v)
  have hVar :
      ((vecVarNN L (u.1 - v.1) : NNReal) : Real) = (dist u v) ^ 2 / (L : Real) ^ 2 := by
    simp [vecVarNN, hdist]
  have hL0 : (L : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hL)
  calc
    (muNN L m rm)[fun omega => Real.exp (l * (X (L := L) (m := m) (rm := rm) u omega -
      X (L := L) (m := m) (rm := rm) v omega))]
        = Real.exp (0 * l + ((vecVarNN L (u.1 - v.1) : NNReal) : Real) * l ^ 2 / 2) := by
            simpa [mgf] using hmgf
    _ = Real.exp (l ^ 2 * ((dist u v) ^ 2 / (L : Real) ^ 2) / 2) := by
          rw [hVar]
          ring_nf
    _ = Real.exp (l ^ 2 * (1 / (L : Real)) ^ 2 * (dist u v) ^ 2 / 2) := by
          congr 1
          field_simp [hL0]
    _ ≤ Real.exp (l ^ 2 * (1 / (L : Real)) ^ 2 * (dist u v) ^ 2 / 2) := by
          exact le_rfl

lemma map_centeredAmbient_diff_gaussian
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (u v : EuclideanSpace Real (Fin m)) :
    (muNN L m rm).map
      (fun omega => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega -
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm v omega)
      = gaussianReal 0 (vecVarNN L (u - v)) := by
  have hSub := M_u_sub (L := L) (m := m) (rm := rm) (u := u) (v := v)
  have hEq :
      (fun omega => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega -
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm v omega)
      = M_u (L := L) (m := m) (rm := rm) (u - v) := by
    funext omega
    unfold centeredAmbientProcess
    have hs := congrArg (fun f => f omega) hSub
    linarith [hs]
  simpa [hEq] using map_M_u_gaussian_any (m := m) (L := L) (rm := rm) hL hrm (u - v)

lemma centeredAmbient_isSubGaussian
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) :
    IsSubGaussianProcess
      (muNN L m rm)
      (centeredAmbientProcess (L := L) (m := m) (rm := rm) hm)
      (1 / (L : Real)) := by
  intro u v l
  have hMap := map_centeredAmbient_diff_gaussian (m := m) (L := L) (rm := rm) hm hL hrm u v
  have hmgf := mgf_gaussianReal
    (p := muNN L m rm)
    (X := fun omega => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega -
      centeredAmbientProcess (L := L) (m := m) (rm := rm) hm v omega)
    (μ := (0 : Real))
    (v := vecVarNN L (u - v))
    hMap l
  have hdist : dist u v = norm (u - v) := by
    simp [dist_eq_norm]
  have hVar : ((vecVarNN L (u - v) : NNReal) : Real) = (dist u v) ^ 2 / (L : Real) ^ 2 := by
    simp [vecVarNN, hdist]
  have hL0 : (L : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hL)
  calc
    (muNN L m rm)[fun omega => Real.exp
      (l * (centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega -
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm v omega))]
        = Real.exp (0 * l + ((vecVarNN L (u - v) : NNReal) : Real) * l ^ 2 / 2) := by
            simpa [mgf] using hmgf
    _ = Real.exp (l ^ 2 * ((dist u v) ^ 2 / (L : Real) ^ 2) / 2) := by
          rw [hVar]
          ring_nf
    _ = Real.exp (l ^ 2 * (1 / (L : Real)) ^ 2 * (dist u v) ^ 2 / 2) := by
          congr 1
          field_simp [hL0]
    _ ≤ Real.exp (l ^ 2 * (1 / (L : Real)) ^ 2 * (dist u v) ^ 2 / 2) := by
          exact le_rfl

lemma measurable_centeredAmbient
    {m L rm : Nat} (hm : 0 < m) (u : EuclideanSpace Real (Fin m)) :
    Measurable (centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u) := by
  unfold centeredAmbientProcess
  exact (measurable_M_u (L := L) (m := m) (rm := rm) u).sub
    (measurable_M_u (L := L) (m := m) (rm := rm) (sphereBaseVec m hm))

lemma integrable_exp_centered_increment
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (u v : EuclideanSpace Real (Fin m)) (l : Real) :
    Integrable
      (fun omega => Real.exp
        (l * (centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega -
          centeredAmbientProcess (L := L) (m := m) (rm := rm) hm v omega)))
      (muNN L m rm) := by
  let dFn : OmegaNN L m rm → Real :=
    fun omega => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega -
      centeredAmbientProcess (L := L) (m := m) (rm := rm) hm v omega
  have hMap : (muNN L m rm).map dFn = gaussianReal 0 (vecVarNN L (u - v)) :=
    map_centeredAmbient_diff_gaussian (m := m) (L := L) (rm := rm) hm hL hrm u v
  have hMeas : AEMeasurable dFn (muNN L m rm) :=
    aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hIntMap : Integrable (fun x : Real => Real.exp (l * x)) ((muNN L m rm).map dFn) := by
    simpa [hMap] using
      (integrable_exp_mul_gaussianReal (μ := (0 : Real)) (v := vecVarNN L (u - v)) l)
  have hComp := (integrable_map_measure hIntMap.aestronglyMeasurable hMeas).mp hIntMap
  simpa [dFn, Function.comp] using hComp

lemma sphere_diam_le_two (m : Nat) :
    Metric.diam (sphereSet m) ≤ 2 := by
  apply Metric.diam_le_of_forall_dist_le (by norm_num)
  intro x hx y hy
  unfold sphereSet at hx hy
  rw [Metric.mem_sphere] at hx hy
  calc
    dist x y = norm (x - y) := by simp [dist_eq_norm]
    _ ≤ norm x + norm y := norm_sub_le _ _
    _ = 2 := by
          have hx' : norm x = 1 := by
            simpa [dist_eq_norm] using hx
          have hy' : norm y = 1 := by
            simpa [dist_eq_norm] using hy
          linarith

lemma continuous_centeredAmbient_on_sphereSet
    {m L rm : Nat} (hm : 0 < m) (omega : OmegaNN L m rm) :
    Continuous
      (fun t : (sphereSet m) => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t.1 omega) := by
  have hContM : Continuous (fun u : EuclideanSpace Real (Fin m) =>
      M_u (L := L) (m := m) (rm := rm) u omega) := by
    unfold M_u meanProbe gLayer deltaH Bfun zfun activationVec
    refine continuous_const.mul ?_
    refine continuous_finset_sum _ ?_
    intro ell _
    refine continuous_finset_sum _ ?_
    intro i _
    have hcoord :
        Continuous (fun u : EuclideanSpace Real (Fin m) => u i) := by
      simpa using (PiLp.continuous_apply 2 (fun _ : Fin m => Real) i)
    exact hcoord.mul continuous_const
  have hContCentered : Continuous (fun u : EuclideanSpace Real (Fin m) =>
      centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u omega) := by
    unfold centeredAmbientProcess
    exact hContM.sub continuous_const
  exact hContCentered.comp continuous_subtype_val

lemma sphereSet_subset_unitBall (m : Nat) :
    Set.Subset (sphereSet m)
      (euclideanBall (ι := Fin m) (1 : Real) : Set (EuclideanSpace Real (Fin m))) := by
  intro x hx
  change dist x 0 <= 1
  unfold sphereSet at hx
  rw [Metric.mem_sphere] at hx
  exact le_of_eq hx

lemma metricEntropy_unitBall_le (m : Nat) (hm : 0 < m) {eps : Real} (heps : 0 < eps) :
    metricEntropy eps (euclideanBall (ι := Fin m) (1 : Real)) <=
      m * Real.log (1 + 2 / eps) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hcov_bound := coveringNumber_euclideanBall_le
    (ι := Fin m) (R := (1 : Real)) (eps := eps) (by norm_num) heps
  have htb : TotallyBounded (euclideanBall (ι := Fin m) (1 : Real)) :=
    euclideanBall_totallyBounded (ι := Fin m) (1 : Real)
  have hfin : coveringNumber eps (euclideanBall (ι := Fin m) (1 : Real)) < ⊤ :=
    coveringNumber_lt_top_of_totallyBounded heps htb
  unfold metricEntropy
  split
  · rename_i htop
    exact (False.elim ((ne_of_lt hfin) htop))
  · rename_i n hn
    have hn_le : (n : Real) <= (1 + 2 / eps) ^ m := by
      simpa [hn] using hcov_bound
    have hN_pos : 1 < (1 + 2 / eps) ^ m := by
      have hbase : 1 < 1 + 2 / eps := by
        have hdiv : 0 < 2 / eps := by positivity
        linarith
      exact one_lt_pow₀ hbase (Nat.pos_iff_ne_zero.mp hm)
    calc
      metricEntropyOfNat n <= Real.log ((1 + 2 / eps) ^ m) :=
        LeastSquares.metricEntropyOfNat_le_log hN_pos hn_le
      _ = m * Real.log (1 + 2 / eps) := by
        rw [Real.log_pow]

lemma dudleyIntegrand_unitBall_le (m : Nat) (hm : 0 < m) {eps : Real} (heps : 0 < eps) :
    dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real)) <=
      ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps))) := by
  unfold dudleyIntegrand
  apply ENNReal.ofReal_le_ofReal
  exact Real.sqrt_le_sqrt (metricEntropy_unitBall_le m hm heps)

lemma entropyIntegral_unitBall_le_explicit (m : Nat) (hm : 0 < m) :
    entropyIntegral (euclideanBall (ι := Fin m) (1 : Real)) 2 <=
      ∫ eps in Set.Ioc 0 (2 : Real), Real.sqrt (m * Real.log (1 + 2 / eps)) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  unfold entropyIntegral entropyIntegralENNReal
  have hbound :
      ∀ eps ∈ Set.Ioc (0 : Real) (2 : Real),
        dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real)) <=
          ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps))) := by
    intro eps heps
    exact dudleyIntegrand_unitBall_le m hm heps.1
  have hmeas : Measurable (fun eps : Real =>
      ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.sqrt
    apply Measurable.mul measurable_const
    apply Real.measurable_log.comp
    apply Measurable.add measurable_const
    apply Measurable.div measurable_const measurable_id
  have hmono :
      ∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
          dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real))
        <=
      ∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
          ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps))) := by
    apply MeasureTheory.setLIntegral_mono hmeas
    intro eps heps
    exact hbound eps heps
  have hint :
      MeasureTheory.IntegrableOn
        (fun eps => Real.sqrt (m * Real.log (1 + 2 / eps)))
        (Set.Ioc 0 (2 : Real)) := by
    simpa using
      (LeastSquares.linearEntropyIntegral_integrableOn
        (d := m) (δ := (1 : Real)) (D := (2 : Real)) (by norm_num) (by norm_num))
  apply ENNReal.toReal_le_of_le_ofReal
  · apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    intro eps heps
    exact Real.sqrt_nonneg _
  calc
    ∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
        dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real))
      <=
    ∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
        ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps))) := hmono
    _ = ENNReal.ofReal
          (∫ eps in Set.Ioc (0 : Real) (2 : Real), Real.sqrt (m * Real.log (1 + 2 / eps))) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
        exact MeasureTheory.ae_of_all _ (fun _ => Real.sqrt_nonneg _)

lemma unitBall_explicit_integral_le_four_sqrt (m : Nat) (hm : 0 < m) :
    (∫ eps in Set.Ioc 0 (2 : Real), Real.sqrt (m * Real.log (1 + 2 / eps))) <=
      4 * Real.sqrt (m : Real) := by
  have hIoc :
      (∫ eps in Set.Ioc 0 (2 : Real), Real.sqrt (m * Real.log (1 + 2 / eps))) =
        ∫ eps in (0 : Real)..2, Real.sqrt (m * Real.log (1 + 2 / eps)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 2)]
  let f : Real -> Real := fun eps => Real.sqrt (m * Real.log (1 + 2 / eps))
  have hSub :
      (∫ eps in (0 : Real)..2, f eps) = 2 * ∫ u in (0 : Real)..1, f (2 * u) := by
    have h := @intervalIntegral.mul_integral_comp_mul_left 0 1 f (2 : Real)
    have h' : 2 * ∫ x in (0 : Real)..1, f (2 * x) = ∫ x in (0 : Real)..2, f x := by
      rw [mul_zero, mul_one] at h
      exact h
    exact h'.symm
  have hSimpPoint :
      ∀ u ∈ Set.Ioo (0 : Real) 1,
        f (2 * u) = Real.sqrt (m * Real.log (1 + 1 / u)) := by
    intro u hu
    have hu0 : (u : Real) ≠ 0 := by exact ne_of_gt hu.1
    have htwo0 : (2 : Real) ≠ 0 := by norm_num
    unfold f
    congr 2
    field_simp [hu0, htwo0]
  have hSimpInt :
      (∫ u in (0 : Real)..1, f (2 * u)) =
        ∫ u in (0 : Real)..1, Real.sqrt (m * Real.log (1 + 1 / u)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1)]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    rcases lt_or_eq_of_le hu.2 with hu1 | hu1
    · exact hSimpPoint u ⟨hu.1, hu1⟩
    · subst hu1
      unfold f
      ring_nf
  have hCmpPoint :
      ∀ u ∈ Set.Ioo (0 : Real) 1,
        Real.sqrt (m * Real.log (1 + 1 / u)) <=
          Real.sqrt (m * Real.log (1 + 2 / u)) := by
    intro u hu
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    apply Real.log_le_log
    · have hu_div : 0 < (1 : Real) / u := by
        exact one_div_pos.mpr hu.1
      linarith
    · have hu_div : (1 : Real) / u <= 2 / u := by
        have hu_nonneg : 0 <= u := le_of_lt hu.1
        exact div_le_div_of_nonneg_right (by norm_num : (1 : Real) <= 2) hu_nonneg
      linarith
  have hIntLeft :
      MeasureTheory.IntegrableOn
        (fun u => Real.sqrt (m * Real.log (1 + 1 / u)))
        (Set.Ioc 0 (1 : Real)) := by
    have h := LeastSquares.linearEntropyIntegral_integrableOn
      (d := m) (δ := (1 / 2 : Real)) (D := (1 : Real)) (by norm_num) (by norm_num)
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hIntRight :
      MeasureTheory.IntegrableOn
        (fun u => Real.sqrt (m * Real.log (1 + 2 / u)))
        (Set.Ioc 0 (1 : Real)) := by
    simpa using
      (LeastSquares.linearEntropyIntegral_integrableOn
        (d := m) (δ := (1 : Real)) (D := (1 : Real)) (by norm_num) (by norm_num))
  have hCmpInt :
      (∫ u in (0 : Real)..1, Real.sqrt (m * Real.log (1 + 1 / u))) <=
        ∫ u in (0 : Real)..1, Real.sqrt (m * Real.log (1 + 2 / u)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1)]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1)]
    exact MeasureTheory.setIntegral_mono_on hIntLeft hIntRight measurableSet_Ioc (by
      intro u hu
      rcases lt_or_eq_of_le hu.2 with hu1 | hu1
      · exact hCmpPoint u ⟨hu.1, hu1⟩
      · subst hu1
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
        apply Real.log_le_log
        · norm_num
        · norm_num)
  have hJ :
      (∫ u in (0 : Real)..1, Real.sqrt (m * Real.log (1 + 2 / u)))
        <= 2 * Real.sqrt (m : Real) := by
    simpa using
      (intermediate_integral_bound
        (n := 1) (d := m) (hn := by norm_num) (hd := hm) (δ := (1 : Real)) (by norm_num))
  calc
    (∫ eps in Set.Ioc 0 (2 : Real), Real.sqrt (m * Real.log (1 + 2 / eps)))
      = ∫ eps in (0 : Real)..2, Real.sqrt (m * Real.log (1 + 2 / eps)) := hIoc
    _ = 2 * ∫ u in (0 : Real)..1, f (2 * u) := hSub
    _ = 2 * ∫ u in (0 : Real)..1, Real.sqrt (m * Real.log (1 + 1 / u)) := by rw [hSimpInt]
    _ <= 2 * ∫ u in (0 : Real)..1, Real.sqrt (m * Real.log (1 + 2 / u)) := by
      gcongr
    _ <= 2 * (2 * Real.sqrt (m : Real)) := by
      gcongr
    _ = 4 * Real.sqrt (m : Real) := by ring

lemma entropyIntegral_unitBall_le (m : Nat) (hm : 0 < m) :
    entropyIntegral (euclideanBall (ι := Fin m) (1 : Real)) 2 <=
      4 * Real.sqrt (m : Real) := by
  exact (entropyIntegral_unitBall_le_explicit m hm).trans (unitBall_explicit_integral_le_four_sqrt m hm)

lemma entropyIntegralENNReal_unitBall_ne_top (m : Nat) (hm : 0 < m) :
    entropyIntegralENNReal (euclideanBall (ι := Fin m) (1 : Real)) 2 ≠ ⊤ := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  unfold entropyIntegralENNReal
  have hbound :
      ∀ eps ∈ Set.Ioc (0 : Real) (2 : Real),
        dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real)) <=
          ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps))) := by
    intro eps heps
    exact dudleyIntegrand_unitBall_le m hm heps.1
  have hmeas : Measurable (fun eps : Real =>
      ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.sqrt
    apply Measurable.mul measurable_const
    apply Real.measurable_log.comp
    apply Measurable.add measurable_const
    apply Measurable.div measurable_const measurable_id
  have hint :
      MeasureTheory.IntegrableOn
        (fun eps => Real.sqrt (m * Real.log (1 + 2 / eps)))
        (Set.Ioc 0 (2 : Real)) := by
    simpa using
      (LeastSquares.linearEntropyIntegral_integrableOn
        (d := m) (δ := (1 : Real)) (D := (2 : Real)) (by norm_num) (by norm_num))
  have hlt :
      (∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
        dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real))) < ⊤ := by
    calc
      (∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
          dudleyIntegrand eps (euclideanBall (ι := Fin m) (1 : Real)))
        <=
      (∫⁻ eps in Set.Ioc (0 : Real) (2 : Real),
          ENNReal.ofReal (Real.sqrt (m * Real.log (1 + 2 / eps)))) := by
            apply MeasureTheory.setLIntegral_mono hmeas
            intro eps heps
            exact hbound eps heps
      _ = ENNReal.ofReal
            (∫ eps in Set.Ioc (0 : Real) (2 : Real), Real.sqrt (m * Real.log (1 + 2 / eps))) := by
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
            exact MeasureTheory.ae_of_all _ (fun _ => Real.sqrt_nonneg _)
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ne_top_of_lt hlt

lemma entropyIntegralENNReal_sphere_ne_top (m : Nat) (hm : 0 < m) :
    entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤ := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hsub : Set.Subset (sphereSet m)
      (euclideanBall (ι := Fin m) (1 : Real) : Set (EuclideanSpace Real (Fin m))) :=
    sphereSet_subset_unitBall m
  have hball_finite : entropyIntegralENNReal
      (euclideanBall (ι := Fin m) (1 : Real)) 2 ≠ ⊤ :=
    entropyIntegralENNReal_unitBall_ne_top m hm
  have hmono : entropyIntegralENNReal (sphereSet m) 2 <=
      entropyIntegralENNReal (euclideanBall (ι := Fin m) (1 : Real)) 2 :=
    entropyIntegralENNReal_mono_set_of_totallyBounded hsub
      (euclideanBall_totallyBounded (ι := Fin m) (1 : Real))
  exact ne_top_of_le_ne_top hball_finite hmono

lemma entropyIntegral_sphere_le (m : Nat) (hm : 0 < m) :
    entropyIntegral (sphereSet m) 2 <= 4 * Real.sqrt (m : Real) := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hsub : Set.Subset (sphereSet m)
      (euclideanBall (ι := Fin m) (1 : Real) : Set (EuclideanSpace Real (Fin m))) :=
    sphereSet_subset_unitBall m
  have hball_finite : entropyIntegralENNReal
      (euclideanBall (ι := Fin m) (1 : Real)) 2 ≠ ⊤ :=
    entropyIntegralENNReal_unitBall_ne_top m hm
  have hmono : entropyIntegral (sphereSet m) 2 <=
      entropyIntegral (euclideanBall (ι := Fin m) (1 : Real)) 2 :=
    entropyIntegral_mono_set_of_totallyBounded hsub
      (euclideanBall_totallyBounded (ι := Fin m) (1 : Real)) hball_finite
  exact hmono.trans (entropyIntegral_unitBall_le m hm)

theorem sphere_process_expected_sup_bound_entropy
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (hfinite : entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤) :
    integral (muNN L m rm)
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega)))
      ≤ (12 * Real.sqrt 2) * (1 / (L : Real)) * entropyIntegral (sphereSet m) 2 := by
  haveI : IsProbabilityMeasure (muNN L m rm) := by
    unfold muNN muG muZ gaussianPi
    infer_instance
  have hsg := centeredAmbient_isSubGaussian (m := m) (L := L) (rm := rm) hm hL hrm
  have hs : TotallyBounded (sphereSet m) := by
    unfold sphereSet
    exact (isCompact_sphere (0 : EuclideanSpace Real (Fin m)) (1 : Real)).totallyBounded
  have hsigma : 0 < (1 / (L : Real)) := by
    have hLReal : (0 : Real) < (L : Real) := by exact_mod_cast hL
    exact one_div_pos.mpr hLReal
  have hdiam : Metric.diam (sphereSet m) ≤ 2 := sphere_diam_le_two m
  have ht0mem : sphereBaseVec m hm ∈ sphereSet m := sphereBaseVec_mem_sphereSet m hm
  have hcenter :
      ∀ omega,
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm (sphereBaseVec m hm) omega = 0 := by
    intro omega
    unfold centeredAmbientProcess
    ring
  have hMeas :
      ∀ t : EuclideanSpace Real (Fin m),
        Measurable (centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t) := by
    intro t
    exact measurable_centeredAmbient (L := L) (m := m) (rm := rm) hm t
  have hIntExp :
      ∀ t s : EuclideanSpace Real (Fin m), ∀ l : Real,
        Integrable
          (fun omega => Real.exp
            (l * (centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega -
              centeredAmbientProcess (L := L) (m := m) (rm := rm) hm s omega)))
          (muNN L m rm) := by
    intro t s l
    exact integrable_exp_centered_increment (L := L) (m := m) (rm := rm) hm hL hrm t s l
  have hCont :
      ∀ omega,
        Continuous
          (fun t : (sphereSet m) => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t.1 omega) := by
    intro omega
    exact continuous_centeredAmbient_on_sphereSet (L := L) (m := m) (rm := rm) hm omega
  have hD : (0 : Real) < 2 := by
    norm_num
  simpa [sphereSet] using
    (dudley
      (μ := muNN L m rm)
      (X := centeredAmbientProcess (L := L) (m := m) (rm := rm) hm)
      (σ := 1 / (L : Real))
      hsigma hsg hs hD hdiam
      (sphereBaseVec m hm) ht0mem hcenter hMeas hIntExp hfinite hCont)

theorem sphere_process_expected_sup_bound_assuming_entropy
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (hfinite : entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤)
    (hEntropy : entropyIntegral (sphereSet m) 2 ≤ 4 * Real.sqrt (m : Real)) :
    integral (muNN L m rm)
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega)))
      ≤ (48 * Real.sqrt 2) * (1 / (L : Real)) * Real.sqrt (m : Real) := by
  have hBase := sphere_process_expected_sup_bound_entropy
    (m := m) (L := L) (rm := rm) hm hL hrm hfinite
  have hScaleNonneg : 0 ≤ (12 * Real.sqrt 2) * (1 / (L : Real)) := by
    have hLReal : (0 : Real) < (L : Real) := by exact_mod_cast hL
    positivity
  calc
    integral (muNN L m rm)
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega)))
      ≤ (12 * Real.sqrt 2) * (1 / (L : Real)) * entropyIntegral (sphereSet m) 2 := hBase
    _ ≤ (12 * Real.sqrt 2) * (1 / (L : Real)) * (4 * Real.sqrt (m : Real)) := by
          gcongr
    _ = (48 * Real.sqrt 2) * (1 / (L : Real)) * Real.sqrt (m : Real) := by
          ring

lemma centered_biSup_eq_centeredSphereSup
    {m L rm : Nat} (hm : 0 < m) (omega : OmegaNN L m rm) :
    (iSup (fun t : EuclideanSpace Real (Fin m) =>
      iSup (fun _ : t ∈ sphereSet m =>
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega))) =
    iSup (fun u : Sphere m =>
      X (L := L) (m := m) (rm := rm) u omega -
        X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  haveI : Nonempty (SphereSetSub m) :=
    Nonempty.intro (sphereToSphereSetSub m (sphereBasePoint m hm))
  have hsne : (sphereSet m).Nonempty :=
    ⟨sphereBaseVec m hm, sphereBaseVec_mem_sphereSet m hm⟩
  have hzero :
      ∃ t ∈ sphereSet m,
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega = 0 := by
    refine ⟨sphereBaseVec m hm, sphereBaseVec_mem_sphereSet m hm, by
      unfold centeredAmbientProcess
      ring⟩
  have hSubtype :
      (iSup (fun t : EuclideanSpace Real (Fin m) =>
        iSup (fun _ : t ∈ sphereSet m =>
          centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega))) =
        iSup (fun t : SphereSetSub m =>
          centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t.1 omega) := by
    simpa [SphereSetSub] using
      (biSup_eq_iSup_subtype_real
        (s := sphereSet m)
        (f := fun t => centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega)
        hsne hzero)
  have hEquiv :
      iSup (fun t : SphereSetSub m =>
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t.1 omega) =
      iSup (fun u : Sphere m =>
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u.1 omega) := by
    let e : SphereSetSub m ≃ Sphere m := (sphereEquivSphereSetSub m).symm
    exact e.iSup_congr (by intro t; rfl)
  have hPoint :
      ∀ u : Sphere m,
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u.1 omega =
          X (L := L) (m := m) (rm := rm) u omega -
            X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega := by
    intro u
    unfold centeredAmbientProcess
    have hu :
        M_u (L := L) (m := m) (rm := rm) u.1 omega =
          X (L := L) (m := m) (rm := rm) u omega := by
      simpa using congrArg (fun f => f omega) (M_u_eq_X (L := L) (m := m) (rm := rm) u)
    have hb :
        M_u (L := L) (m := m) (rm := rm) (sphereBaseVec m hm) omega =
          X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega := by
      simpa [sphereBasePoint] using congrArg (fun f => f omega)
        (M_u_eq_X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm))
    rw [hu, hb]
  have hSphere :
      iSup (fun u : Sphere m =>
        centeredAmbientProcess (L := L) (m := m) (rm := rm) hm u.1 omega) =
      iSup (fun u : Sphere m =>
        X (L := L) (m := m) (rm := rm) u omega -
          X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) := by
    refine iSup_congr ?_
    intro u
    exact hPoint u
  exact hSubtype.trans (hEquiv.trans hSphere)

lemma map_X_base_gaussian
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) :
    (muNN L m rm).map (fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) =
      gaussianReal 0 (vecVarNN L (sphereBaseVec m hm)) := by
  have hMap := map_M_u_gaussian_any (m := m) (L := L) (rm := rm) hL hrm (sphereBaseVec m hm)
  have hEq :
      (fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) =
        M_u (L := L) (m := m) (rm := rm) (sphereBaseVec m hm) := by
    funext omega
    have hb := congrArg (fun f => f omega)
      (M_u_eq_X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm))
    simpa [sphereBasePoint] using hb.symm
  simpa [hEq] using hMap

lemma W_coord_eq_M_u_single
    {m L rm : Nat} (i : Fin m) :
    (fun omega : OmegaNN L m rm => W (L := L) (m := m) (rm := rm) omega i) =
      M_u (L := L) (m := m) (rm := rm) (EuclideanSpace.single i (1 : Real)) := by
  funext omega
  have hInner := congrArg (fun f => f omega)
    (M_u_eq_inner_W (L := L) (m := m) (rm := rm) (EuclideanSpace.single i (1 : Real)))
  simpa [EuclideanSpace.single_apply] using hInner.symm

lemma measurable_W_coord
    {m L rm : Nat} (i : Fin m) :
    Measurable (fun omega : OmegaNN L m rm => W (L := L) (m := m) (rm := rm) omega i) := by
  have hM :
      Measurable (M_u (L := L) (m := m) (rm := rm) (EuclideanSpace.single i (1 : Real))) :=
    measurable_M_u (L := L) (m := m) (rm := rm) (EuclideanSpace.single i (1 : Real))
  simpa [W_coord_eq_M_u_single (m := m) (L := L) (rm := rm) i] using hM

lemma integrable_W_coord
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm) (i : Fin m) :
    Integrable
      (fun omega : OmegaNN L m rm => W (L := L) (m := m) (rm := rm) omega i)
      (muNN L m rm) := by
  let f : OmegaNN L m rm → Real :=
    fun omega => W (L := L) (m := m) (rm := rm) omega i
  have hu : norm (EuclideanSpace.single i (1 : Real)) = 1 := by
    simp [EuclideanSpace.norm_single]
  have hMap :
      (muNN L m rm).map f = gaussianReal 0 (invLSqNNReal L) := by
    have hMapM := scalar_mean_map_gaussian (m := m) (L := L) (rm := rm) hL hrm
      (EuclideanSpace.single i (1 : Real)) hu
    simpa [f, W_coord_eq_M_u_single (m := m) (L := L) (rm := rm) i] using hMapM
  have hMem : MemLp (fun x : Real => x) 1 ((muNN L m rm).map f) := by
    rw [hMap]
    simpa using (@ProbabilityTheory.memLp_id_gaussianReal
      (0 : Real) (invLSqNNReal L) (1 : NNReal))
  have hIntMap : Integrable (fun x : Real => x) ((muNN L m rm).map f) :=
    (memLp_one_iff_integrable).mp hMem
  have hMeas : AEMeasurable f (muNN L m rm) := by
    exact aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hIntComp : Integrable (Function.comp (fun x : Real => x) f) (muNN L m rm) := by
    exact (integrable_map_measure (f := f) (g := fun x : Real => x)
      aestronglyMeasurable_id hMeas).mp hIntMap
  simpa [f, Function.comp] using hIntComp

lemma integrable_sum_absW
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm) :
    Integrable
      (fun omega : OmegaNN L m rm =>
        ∑ i : Fin m, |W (L := L) (m := m) (rm := rm) omega i|)
      (muNN L m rm) := by
  simpa using
    (MeasureTheory.integrable_finset_sum (μ := muNN L m rm) (s := (Finset.univ : Finset (Fin m)))
      (fun i hi => (integrable_W_coord (m := m) (L := L) (rm := rm) hL hrm i).abs))

lemma integrable_X_base
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) :
    Integrable
      (fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)
      (muNN L m rm) := by
  let f : OmegaNN L m rm -> Real :=
    fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega
  have hMap : (muNN L m rm).map f = gaussianReal 0 (vecVarNN L (sphereBaseVec m hm)) := by
    simpa [f] using map_X_base_gaussian (m := m) (L := L) (rm := rm) hm hL hrm
  have hMem : MemLp (fun x : Real => x) 1 ((muNN L m rm).map f) := by
    rw [hMap]
    simpa using (@ProbabilityTheory.memLp_id_gaussianReal
      (0 : Real) (vecVarNN L (sphereBaseVec m hm)) (1 : NNReal))
  have hIntMap : Integrable (fun x : Real => x) ((muNN L m rm).map f) :=
    (memLp_one_iff_integrable).mp hMem
  have hMeas : AEMeasurable f (muNN L m rm) := by
    exact aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hIntComp : Integrable (Function.comp (fun x : Real => x) f) (muNN L m rm) := by
    exact (integrable_map_measure (f := f) (g := fun x : Real => x)
      aestronglyMeasurable_id hMeas).mp hIntMap
  simpa [f, Function.comp] using hIntComp

lemma integral_X_base_eq_zero
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) :
    integral (muNN L m rm)
      (fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) = 0 := by
  let f : OmegaNN L m rm → Real :=
    fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega
  have hMap : (muNN L m rm).map f = gaussianReal 0 (vecVarNN L (sphereBaseVec m hm)) := by
    simpa [f] using map_X_base_gaussian (m := m) (L := L) (rm := rm) hm hL hrm
  have hMeas : AEMeasurable f (muNN L m rm) := by
    exact aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hMapIntegral :
      integral ((muNN L m rm).map f) (fun x : Real => x) =
        integral (muNN L m rm) (fun omega => f omega) := by
    simpa using (integral_map hMeas (f := fun x : Real => x) aestronglyMeasurable_id)
  calc
    integral (muNN L m rm) (fun omega => f omega)
        = integral ((muNN L m rm).map f) (fun x : Real => x) := by
            exact hMapIntegral.symm
    _ = integral (gaussianReal 0 (vecVarNN L (sphereBaseVec m hm))) (fun x : Real => x) := by
          rw [hMap]
    _ = 0 := by
          simp [integral_id_gaussianReal]

lemma bddAbove_X_range
    {m L rm : Nat} (omega : OmegaNN L m rm) :
    BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) := by
  refine Exists.intro
    (Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)))
    ?_
  intro y hy
  rcases hy with ⟨u, hu⟩
  rw [← hu]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
    (fun i => u.1 i) (fun i => W (L := L) (m := m) (rm := rm) omega i)
  have huSqrt : Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) = 1 := by
    calc
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2))
          = norm u.1 := by
              symm
              simpa using (EuclideanSpace.norm_eq u.1)
      _ = 1 := u.2
  calc
    X (L := L) (m := m) (rm := rm) u omega
        = Finset.univ.sum (fun i : Fin m => u.1 i * W (L := L) (m := m) (rm := rm) omega i) := by
            rfl
    _ <= Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) *
          Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          simpa using hcs
    _ = Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          rw [huSqrt, one_mul]

lemma supX_nonneg
    {m L rm : Nat} (hm : 0 < m) (omega : OmegaNN L m rm) :
    0 <= iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  have hBdd : BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) :=
    bddAbove_X_range (L := L) (m := m) (rm := rm) omega
  let u0 : Sphere m := sphereBasePoint m hm
  let uNeg : Sphere m := ⟨-u0.1, by simpa [norm_neg] using u0.2⟩
  have hu0 : X (L := L) (m := m) (rm := rm) u0 omega <=
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) := by
    exact le_ciSup hBdd u0
  have huNeg : X (L := L) (m := m) (rm := rm) uNeg omega <=
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) := by
    exact le_ciSup hBdd uNeg
  have huNegEq :
      X (L := L) (m := m) (rm := rm) uNeg omega =
        -X (L := L) (m := m) (rm := rm) u0 omega := by
    dsimp [uNeg, u0]
    unfold X
    simp
  linarith [hu0, huNegEq, huNeg]

lemma supX_le_sum_absW
    {m L rm : Nat} (hm : 0 < m) (omega : OmegaNN L m rm) :
    iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) <=
      ∑ i : Fin m, |W (L := L) (m := m) (rm := rm) omega i| := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  have hBdd : BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) :=
    bddAbove_X_range (L := L) (m := m) (rm := rm) omega
  refine ciSup_le ?_
  intro u
  have hcoord : ∀ i : Fin m, |u.1 i| <= 1 := by
    intro i
    have hinner :
        |inner ℝ u.1 (EuclideanSpace.single i (1 : Real))| <=
          ‖u.1‖ * ‖EuclideanSpace.single i (1 : Real)‖ :=
      abs_real_inner_le_norm u.1 (EuclideanSpace.single i (1 : Real))
    have hpi : |u.1 i| <= ‖u.1‖ := by
      calc
        |u.1 i| <= ‖u.1‖ * ‖EuclideanSpace.single i (1 : Real)‖ := by
          simpa [EuclideanSpace.inner_single_right] using hinner
        _ = ‖u.1‖ := by
          simp [EuclideanSpace.norm_single]
    simpa [u.2] using hpi
  calc
    X (L := L) (m := m) (rm := rm) u omega
        <= |X (L := L) (m := m) (rm := rm) u omega| := le_abs_self _
    _ = |∑ i : Fin m, u.1 i * W (L := L) (m := m) (rm := rm) omega i| := by rfl
    _ <= ∑ i : Fin m, |u.1 i * W (L := L) (m := m) (rm := rm) omega i| := by
          simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin m =>
            u.1 i * W (L := L) (m := m) (rm := rm) omega i) Finset.univ)
    _ = ∑ i : Fin m, |u.1 i| * |W (L := L) (m := m) (rm := rm) omega i| := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact abs_mul (u.1 i) (W (L := L) (m := m) (rm := rm) omega i)
    _ <= ∑ i : Fin m, 1 * |W (L := L) (m := m) (rm := rm) omega i| := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg _)
    _ = ∑ i : Fin m, |W (L := L) (m := m) (rm := rm) omega i| := by
          simp

lemma measurable_sqrt_sumWsq
    {m L rm : Nat} :
    Measurable (fun omega : OmegaNN L m rm =>
      Real.sqrt (Finset.univ.sum
        (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2))) := by
  apply Measurable.sqrt
  refine Finset.measurable_sum (s := (Finset.univ : Finset (Fin m))) ?_
  intro i hi
  exact (measurable_W_coord (m := m) (L := L) (rm := rm) i).pow_const 2

lemma X_le_sqrt_sumWsq_aux
    {m L rm : Nat} (u : Sphere m) (omega : OmegaNN L m rm) :
    X (L := L) (m := m) (rm := rm) u omega <=
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
    (fun i => u.1 i) (fun i => W (L := L) (m := m) (rm := rm) omega i)
  have huSqrt : Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) = 1 := by
    calc
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2))
          = norm u.1 := by
              symm
              simpa using (EuclideanSpace.norm_eq u.1)
      _ = 1 := u.2
  calc
    X (L := L) (m := m) (rm := rm) u omega
        = Finset.univ.sum (fun i : Fin m => u.1 i * W (L := L) (m := m) (rm := rm) omega i) := by rfl
    _ <= Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) *
          Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          simpa using hcs
    _ = Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          rw [huSqrt, one_mul]

lemma supX_eq_sqrt_sumWsq
    {m L rm : Nat} (hm : 0 < m) (omega : OmegaNN L m rm) :
    iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) =
      Real.sqrt (Finset.univ.sum
        (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  have hBdd : BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) :=
    bddAbove_X_range (L := L) (m := m) (rm := rm) omega
  let s : Real := Real.sqrt (Finset.univ.sum
    (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2))
  have hUpper :
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) <=
      s := by
    refine ciSup_le ?_
    intro u
    simpa [s] using X_le_sqrt_sumWsq_aux (L := L) (m := m) (rm := rm) u omega
  let w : EuclideanSpace Real (Fin m) :=
    (EuclideanSpace.equiv (Fin m) Real).symm (W (L := L) (m := m) (rm := rm) omega)
  have hw_apply : ∀ i : Fin m, w i = W (L := L) (m := m) (rm := rm) omega i := by
    intro i
    simp [w]
  have hs_nonneg : 0 <= s := by
    exact Real.sqrt_nonneg _
  have hsq : s ^ 2 = Finset.univ.sum
      (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2) := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hnormW : norm w = s := by
    calc
      norm w = Real.sqrt (Finset.univ.sum (fun i : Fin m => (w i) ^ 2)) := by
        simpa using (EuclideanSpace.norm_eq w)
      _ = Real.sqrt (Finset.univ.sum
          (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          refine congrArg Real.sqrt ?_
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hw_apply i]
      _ = s := by
          rfl
  have hLower :
      s <= iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) := by
    by_cases hs0 : s = 0
    · have hsup_nonneg :
        0 <= iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) :=
        supX_nonneg (m := m) (L := L) (rm := rm) hm omega
      linarith
    · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs0)
      let uVec : EuclideanSpace Real (Fin m) := (1 / s) • w
      have huNorm : norm uVec = 1 := by
        calc
          norm uVec = |1 / s| * norm w := by
            simp [uVec, norm_smul]
          _ = (1 / s) * s := by
            rw [abs_of_pos (one_div_pos.mpr hs_pos), hnormW]
          _ = 1 := by
            field_simp [hs0]
      let uSphere : Sphere m := ⟨uVec, huNorm⟩
      have huLe : X (L := L) (m := m) (rm := rm) uSphere omega <=
          iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) := by
        exact le_ciSup hBdd uSphere
      have hXu : X (L := L) (m := m) (rm := rm) uSphere omega = s := by
        calc
          X (L := L) (m := m) (rm := rm) uSphere omega
              = ∑ i : Fin m, (uVec i) * W (L := L) (m := m) (rm := rm) omega i := by
                  rfl
          _ = ∑ i : Fin m, ((1 / s) * w i) * W (L := L) (m := m) (rm := rm) omega i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [uVec]
          _ = ∑ i : Fin m, ((1 / s) * W (L := L) (m := m) (rm := rm) omega i) *
              W (L := L) (m := m) (rm := rm) omega i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hw_apply i]
          _ = ∑ i : Fin m, (1 / s) *
              (W (L := L) (m := m) (rm := rm) omega i *
                W (L := L) (m := m) (rm := rm) omega i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
          _ = (1 / s) * ∑ i : Fin m,
              (W (L := L) (m := m) (rm := rm) omega i *
                W (L := L) (m := m) (rm := rm) omega i) := by
                rw [Finset.mul_sum]
          _ = (1 / s) * ∑ i : Fin m, (W (L := L) (m := m) (rm := rm) omega i) ^ 2 := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
          _ = (1 / s) * s ^ 2 := by rw [hsq]
          _ = s := by
                field_simp [hs0]
      linarith [huLe, hXu]
  calc
    iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)
        = s := le_antisymm hUpper hLower
    _ = Real.sqrt (Finset.univ.sum
          (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          simp [s]

lemma integrable_supX
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) :
    Integrable
      (fun omega : OmegaNN L m rm =>
        iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega))
      (muNN L m rm) := by
  let supX : OmegaNN L m rm → Real :=
    fun omega => iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)
  let sumAbsW : OmegaNN L m rm → Real :=
    fun omega => ∑ i : Fin m, |W (L := L) (m := m) (rm := rm) omega i|
  have hIntDom : Integrable sumAbsW (muNN L m rm) := by
    simpa [sumAbsW] using integrable_sum_absW (m := m) (L := L) (rm := rm) hL hrm
  have hAesmSup : AEStronglyMeasurable supX (muNN L m rm) := by
    have hMeasRhs :
        Measurable (fun omega : OmegaNN L m rm =>
          Real.sqrt (Finset.univ.sum
            (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2))) :=
      measurable_sqrt_sumWsq (m := m) (L := L) (rm := rm)
    have hAesmRhs :
        AEStronglyMeasurable
          (fun omega : OmegaNN L m rm =>
            Real.sqrt (Finset.univ.sum
              (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)))
          (muNN L m rm) := hMeasRhs.aestronglyMeasurable
    refine hAesmRhs.congr ?_
    exact Filter.Eventually.of_forall (fun omega =>
      (supX_eq_sqrt_sumWsq (m := m) (L := L) (rm := rm) hm omega).symm)
  have hDom :
      ∀ᵐ omega ∂(muNN L m rm), ‖supX omega‖ <= sumAbsW omega := by
    refine Filter.Eventually.of_forall ?_
    intro omega
    have hLe : supX omega <= sumAbsW omega := by
      simpa [supX, sumAbsW] using
        supX_le_sum_absW (m := m) (L := L) (rm := rm) hm omega
    have hNonneg : 0 <= supX omega := by
      simpa [supX] using supX_nonneg (m := m) (L := L) (rm := rm) hm omega
    have hEqAbs : |supX omega| = supX omega := abs_of_nonneg hNonneg
    have hSumNonneg : 0 <= sumAbsW omega := by
      dsimp [sumAbsW]
      exact Finset.sum_nonneg (fun i hi => abs_nonneg _)
    calc
      ‖supX omega‖ = |supX omega| := by simp [Real.norm_eq_abs]
      _ = supX omega := hEqAbs
      _ <= sumAbsW omega := hLe
  exact Integrable.mono' hIntDom hAesmSup hDom

lemma X_le_sqrt_sumWsq
    {m L rm : Nat} (u : Sphere m) (omega : OmegaNN L m rm) :
    X (L := L) (m := m) (rm := rm) u omega <=
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
    (fun i => u.1 i) (fun i => W (L := L) (m := m) (rm := rm) omega i)
  have huSqrt : Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) = 1 := by
    calc
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2))
          = norm u.1 := by
              symm
              simpa using (EuclideanSpace.norm_eq u.1)
      _ = 1 := u.2
  calc
    X (L := L) (m := m) (rm := rm) u omega
        = Finset.univ.sum (fun i : Fin m => u.1 i * W (L := L) (m := m) (rm := rm) omega i) := by rfl
    _ <= Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) *
          Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          simpa using hcs
    _ = Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
          rw [huSqrt, one_mul]

lemma sphere_sup_event_subset_union_coords
    {m L rm : Nat} (hm : 0 < m) (t : Real) (ht : 0 < t) :
    Set.Subset
      {omega : OmegaNN L m rm |
        t <= iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)}
      (Set.iUnion (fun i : Fin m =>
        {omega : OmegaNN L m rm |
          t / Real.sqrt (m : Real) <=
            |W (L := L) (m := m) (rm := rm) omega i|})) := by
  intro omega hsup
  by_contra hnot
  have hall : forall i : Fin m,
      |W (L := L) (m := m) (rm := rm) omega i| < t / Real.sqrt (m : Real) := by
    intro i
    exact lt_of_not_ge (by
      intro hi
      exact hnot (Set.mem_iUnion.2 (Exists.intro i hi)))
  have hsq : forall i : Fin m,
      (W (L := L) (m := m) (rm := rm) omega i) ^ 2 < t ^ 2 / (m : Real) := by
    intro i
    have hi := hall i
    have hi_abs : (W (L := L) (m := m) (rm := rm) omega i) ^ 2 < (t / Real.sqrt (m : Real)) ^ 2 := by
      have hi' := abs_lt.mp hi
      nlinarith
    have hm0 : (m : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hsqrt_sq : (Real.sqrt (m : Real)) ^ 2 = (m : Real) := by
      exact Real.sq_sqrt (by positivity)
    have hsqrt0 : Real.sqrt (m : Real) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      exact_mod_cast hm
    have hdiv_sq : (t / Real.sqrt (m : Real)) ^ 2 = t ^ 2 / (m : Real) := by
      field_simp [hsqrt0]
      ring_nf
      rw [hsqrt_sq]
    rwa [hdiv_sq] at hi_abs
  have hsum_lt :
      Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)
        < Finset.univ.sum (fun _ : Fin m => t ^ 2 / (m : Real)) := by
    classical
    have hlt : ∃ i ∈ (Finset.univ : Finset (Fin m)),
        (W (L := L) (m := m) (rm := rm) omega i) ^ 2 < t ^ 2 / (m : Real) := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      exact ⟨Classical.choice ‹Nonempty (Fin m)›, Finset.mem_univ _, hsq _⟩
    exact Finset.sum_lt_sum (fun i _ => le_of_lt (hsq i)) hlt
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hsum_const :
      Finset.univ.sum (fun _ : Fin m => t ^ 2 / (m : Real)) = t ^ 2 := by
    calc
      Finset.univ.sum (fun _ : Fin m => t ^ 2 / (m : Real))
          = (Fintype.card (Fin m) : Real) * (t ^ 2 / (m : Real)) := by simp
      _ = (m : Real) * (t ^ 2 / (m : Real)) := by simp
      _ = t ^ 2 := by field_simp [hm0]
  have hsumW_lt :
      Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2) < t ^ 2 := by
    simpa [hsum_const] using hsum_lt
  have hsqrtW_lt :
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) < t := by
    have hnonneg : 0 <= Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2) := by
      positivity
    exact (Real.sqrt_lt hnonneg (le_of_lt ht)).2 hsumW_lt
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  have hBdd : BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) :=
    bddAbove_X_range (L := L) (m := m) (rm := rm) omega
  have hsup_le :
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)
        <= Real.sqrt (Finset.univ.sum (fun i : Fin m => (W (L := L) (m := m) (rm := rm) omega i) ^ 2)) := by
    refine ciSup_le ?_
    intro u
    exact X_le_sqrt_sumWsq (L := L) (m := m) (rm := rm) u omega
  have hsup_lt :
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) < t := lt_of_le_of_lt hsup_le hsqrtW_lt
  exact (not_le_of_gt hsup_lt) hsup

lemma sphere_sup_eq_centered_add_base
    {m L rm : Nat} (hm : 0 < m) (omega : OmegaNN L m rm) :
    iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) =
      iSup (fun u : Sphere m =>
        X (L := L) (m := m) (rm := rm) u omega -
          X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) +
        X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  set b : Real := X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega
  have hBddX : BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) :=
    bddAbove_X_range (L := L) (m := m) (rm := rm) omega
  have hBddCentered : BddAbove
      (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega - b)) := by
    rcases hBddX with ⟨M, hM⟩
    refine ⟨M - b, ?_⟩
    intro y hy
    rcases hy with ⟨u, hu⟩
    rw [← hu]
    have huM : X (L := L) (m := m) (rm := rm) u omega <= M := hM ⟨u, rfl⟩
    linarith
  have hUpper :
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) <=
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega - b) + b := by
    refine ciSup_le ?_
    intro u
    have huLe :
        X (L := L) (m := m) (rm := rm) u omega - b <=
          iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega - b) :=
      le_ciSup hBddCentered u
    linarith
  have hLower :
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega - b) + b <=
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) := by
    have hTmp :
        iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega - b) <=
          iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) - b := by
      refine ciSup_le ?_
      intro u
      have huLe :
          X (L := L) (m := m) (rm := rm) u omega <=
            iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) :=
        le_ciSup hBddX u
      linarith
    linarith
  have hMain :
      iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega) =
        iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega - b) + b :=
    le_antisymm hUpper hLower
  simpa [b] using hMain

theorem sphere_process_expected_sup_bound
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) :
    integral (muNN L m rm) (fun omega => iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega))
      <= (48 * Real.sqrt 2) * (Real.sqrt (m : Real) / (L : Real)) := by
  let supX : OmegaNN L m rm → Real :=
    fun omega => iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)
  have hfinite : entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤ :=
    entropyIntegralENNReal_sphere_ne_top m hm
  have hEntropy : entropyIntegral (sphereSet m) 2 <= 4 * Real.sqrt (m : Real) :=
    entropyIntegral_sphere_le m hm
  have hCenteredRaw := sphere_process_expected_sup_bound_assuming_entropy
    (m := m) (L := L) (rm := rm) hm hL hrm hfinite hEntropy
  have hIntegrandEq :
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredAmbientProcess (L := L) (m := m) (rm := rm) hm t omega))) =
      (fun omega =>
        iSup (fun u : Sphere m =>
          X (L := L) (m := m) (rm := rm) u omega -
            X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)) := by
    funext omega
    exact centered_biSup_eq_centeredSphereSup (m := m) (L := L) (rm := rm) hm omega
  have hCentered :
      integral (muNN L m rm)
        (fun omega =>
          iSup (fun u : Sphere m =>
            X (L := L) (m := m) (rm := rm) u omega -
              X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega))
      <= (48 * Real.sqrt 2) * (1 / (L : Real)) * Real.sqrt (m : Real) := by
    simpa [hIntegrandEq] using hCenteredRaw
  have hIntSup : Integrable supX (muNN L m rm) :=
    integrable_supX (m := m) (L := L) (rm := rm) hm hL hrm
  have hIntBase := integrable_X_base (m := m) (L := L) (rm := rm) hm hL hrm
  have hCenteredSubEq :
      (fun omega =>
        iSup (fun u : Sphere m =>
          X (L := L) (m := m) (rm := rm) u omega -
            X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)) =
      (fun omega =>
        supX omega -
          X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) := by
    funext omega
    dsimp [supX]
    linarith [sphere_sup_eq_centered_add_base (m := m) (L := L) (rm := rm) hm omega]
  have hIntCenteredSub : Integrable
      (fun omega =>
        supX omega -
          X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)
      (muNN L m rm) := hIntSup.sub hIntBase
  have hIntCentered : Integrable
      (fun omega =>
        iSup (fun u : Sphere m =>
          X (L := L) (m := m) (rm := rm) u omega -
            X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega))
      (muNN L m rm) := by
    refine Integrable.congr hIntCenteredSub ?_
    exact Filter.Eventually.of_forall (fun omega =>
      (congrArg (fun f => f omega) hCenteredSubEq).symm)
  have hAddEq :
      (fun omega => supX omega) =
      (fun omega =>
        iSup (fun u : Sphere m =>
          X (L := L) (m := m) (rm := rm) u omega -
            X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) +
          X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) := by
    funext omega
    dsimp [supX]
    exact sphere_sup_eq_centered_add_base (m := m) (L := L) (rm := rm) hm omega
  have hIntegralSplit :
      integral (muNN L m rm) (fun omega => supX omega)
      =
      integral (muNN L m rm)
        (fun omega =>
          iSup (fun u : Sphere m =>
            X (L := L) (m := m) (rm := rm) u omega -
              X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)) +
        integral (muNN L m rm)
          (fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) := by
    rw [hAddEq]
    exact integral_add hIntCentered hIntBase
  have hBaseZero := integral_X_base_eq_zero (m := m) (L := L) (rm := rm) hm hL hrm
  calc
    integral (muNN L m rm)
      (fun omega => iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega))
        = integral (muNN L m rm) (fun omega => supX omega) := by
            rfl
    _ =
      integral (muNN L m rm)
        (fun omega =>
          iSup (fun u : Sphere m =>
            X (L := L) (m := m) (rm := rm) u omega -
              X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)) +
      integral (muNN L m rm)
        (fun omega => X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega) := hIntegralSplit
    _ =
      integral (muNN L m rm)
        (fun omega =>
          iSup (fun u : Sphere m =>
            X (L := L) (m := m) (rm := rm) u omega -
              X (L := L) (m := m) (rm := rm) (sphereBasePoint m hm) omega)) := by
          rw [hBaseZero, add_zero]
    _ <= (48 * Real.sqrt 2) * (1 / (L : Real)) * Real.sqrt (m : Real) := hCentered
    _ = (48 * Real.sqrt 2) * (Real.sqrt (m : Real) / (L : Real)) := by
          ring
theorem sphere_process_highProb_bound
    {m L rm : Nat} (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm) (t : Real) (ht : 0 < t) :
    ((muNN L m rm) {omega |
      integral (muNN L m rm)
          (fun w => iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u w)) + t <=
        iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)}).toReal <=
      2 * (m : Real) * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2) := by
  haveI : IsProbabilityMeasure (muNN L m rm) := by
    unfold muNN muG muZ gaussianPi
    infer_instance
  let supX : OmegaNN L m rm -> Real := fun omega =>
    iSup (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)
  let Amean : Set (OmegaNN L m rm) := {omega |
    integral (muNN L m rm) supX + t <= supX omega}
  let A : Set (OmegaNN L m rm) := {omega | t <= supX omega}
  let B : Fin m -> Set (OmegaNN L m rm) := fun i =>
    {omega | t / Real.sqrt (m : Real) <= |W (L := L) (m := m) (rm := rm) omega i|}
  have hSup_nonneg : ∀ omega, 0 <= supX omega := by
    intro omega
    haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
    have hBdd : BddAbove (Set.range (fun u : Sphere m => X (L := L) (m := m) (rm := rm) u omega)) :=
      bddAbove_X_range (L := L) (m := m) (rm := rm) omega
    let u0 : Sphere m := sphereBasePoint m hm
    let uNeg : Sphere m := ⟨-u0.1, by simpa [norm_neg] using u0.2⟩
    have hu0 : X (L := L) (m := m) (rm := rm) u0 omega <= supX omega := by
      exact le_ciSup hBdd u0
    have huNeg : X (L := L) (m := m) (rm := rm) uNeg omega <= supX omega := by
      exact le_ciSup hBdd uNeg
    have huNegEq :
        X (L := L) (m := m) (rm := rm) uNeg omega =
          -X (L := L) (m := m) (rm := rm) u0 omega := by
      dsimp [uNeg, u0]
      unfold X
      simp
    linarith [hu0, huNegEq, huNeg]
  have hES_nonneg : 0 <= integral (muNN L m rm) supX := by
    exact integral_nonneg hSup_nonneg
  have hAmean_subset_A : Amean ⊆ A := by
    intro omega homega
    have ht_le : t <= integral (muNN L m rm) supX + t := by linarith
    exact le_trans ht_le homega
  have hA_subset_union : A ⊆ Set.iUnion B := by
    simpa [A, B, supX] using
      sphere_sup_event_subset_union_coords (m := m) (L := L) (rm := rm) hm t ht
  have h_union :
      (muNN L m rm) A <= (muNN L m rm) (Set.iUnion B) := measure_mono hA_subset_union
  have h_union_sum :
      (muNN L m rm) (Set.iUnion B) <= ∑ i : Fin m, (muNN L m rm) (B i) := by
    calc
      (muNN L m rm) (Set.iUnion B) <= ∑' i : Fin m, (muNN L m rm) (B i) := measure_iUnion_le B
      _ = ∑ i : Fin m, (muNN L m rm) (B i) := by
            simp [tsum_fintype]
  have hsum_ne_top : (∑ i : Fin m, (muNN L m rm) (B i)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 (fun i hi => measure_ne_top _ _)
  have hA_toReal :
      ((muNN L m rm) A).toReal <= (∑ i : Fin m, (muNN L m rm) (B i)).toReal := by
    exact ENNReal.toReal_mono hsum_ne_top (h_union.trans h_union_sum)
  have hsum_toReal :
      (∑ i : Fin m, (muNN L m rm) (B i)).toReal =
        ∑ i : Fin m, ((muNN L m rm) (B i)).toReal := by
    simpa using
      (ENNReal.toReal_sum (s := (Finset.univ : Finset (Fin m)))
        (f := fun i : Fin m => (muNN L m rm) (B i))
        (fun i hi => measure_ne_top _ _))
  have hcoord :
      ∀ i : Fin m,
        ((muNN L m rm) (B i)).toReal <=
          2 * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2) := by
    intro i
    have hu : norm (EuclideanSpace.single i (1 : Real)) = 1 := by
      simp [EuclideanSpace.norm_single]
    have htScaled : 0 < t / Real.sqrt (m : Real) := by
      have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
      positivity
    have htail :=
      scalar_mean_tail (m := m) (L := L) (rm := rm) hL hrm
        (EuclideanSpace.single i (1 : Real)) hu
        (t / Real.sqrt (m : Real)) htScaled
    have hMuWi :
        ∀ omega : OmegaNN L m rm,
          M_u (L := L) (m := m) (rm := rm) (EuclideanSpace.single i (1 : Real)) omega =
            W (L := L) (m := m) (rm := rm) omega i := by
      intro omega
      have hInner := congrArg (fun f => f omega)
        (M_u_eq_inner_W (L := L) (m := m) (rm := rm) (EuclideanSpace.single i (1 : Real)))
      simpa [EuclideanSpace.single_apply] using hInner
    simpa [B, hMuWi, ge_iff_le] using htail
  have hsum_coord :
      (∑ i : Fin m, ((muNN L m rm) (B i)).toReal) <=
        ∑ i : Fin m, (2 * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2)) := by
    exact Finset.sum_le_sum (fun i hi => hcoord i)
  have hsum_const :
      (∑ i : Fin m, (2 * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2)))
        = 2 * (m : Real) * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2) := by
    simp [Finset.card_univ, mul_assoc, mul_comm]
  calc
    ((muNN L m rm) Amean).toReal
        <= ((muNN L m rm) A).toReal := by
            exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hAmean_subset_A)
    _ <= (∑ i : Fin m, (muNN L m rm) (B i)).toReal := hA_toReal
    _ = ∑ i : Fin m, ((muNN L m rm) (B i)).toReal := hsum_toReal
    _ <= ∑ i : Fin m, (2 * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2)) := hsum_coord
    _ = 2 * (m : Real) * Real.exp (-(L : Real) ^ 2 * (t / Real.sqrt (m : Real)) ^ 2 / 2) := hsum_const

end

end NNGPResNet
end LeanSlt
