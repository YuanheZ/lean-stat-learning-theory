import LeanSlt.NNGPResNet.Correlated.Scalar
import LeanSlt.NNGPResNet.SphereChaining
import SLT.Dudley

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet
namespace Correlated

noncomputable section

def centeredCorrProcess {L m rm : Nat} (hm : 0 < m)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (omega : OmegaCorr L m rm) : Real :=
  M_u_corr (L := L) (m := m) (rm := rm) A u omega -
    M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega

lemma M_u_corr_sub
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u v : EuclideanSpace Real (Fin m)) :
    M_u_corr (L := L) (m := m) (rm := rm) A (u - v)
      = fun omega =>
          M_u_corr (L := L) (m := m) (rm := rm) A u omega -
            M_u_corr (L := L) (m := m) (rm := rm) A v omega := by
  funext omega
  unfold M_u_corr
  have hterm :
      (fun idx : LatentIdx L m rm =>
        corrScale L rm * (u - v) idx.2.1 * sumACol A idx.1 *
          aCoord omega idx.2.2 * latentCoord omega idx.1 idx.2.1 idx.2.2) =
      (fun idx : LatentIdx L m rm =>
        corrScale L rm * u idx.2.1 * sumACol A idx.1 *
            aCoord omega idx.2.2 * latentCoord omega idx.1 idx.2.1 idx.2.2 -
          corrScale L rm * v idx.2.1 * sumACol A idx.1 *
            aCoord omega idx.2.2 * latentCoord omega idx.1 idx.2.1 idx.2.2) := by
    funext idx
    have hsub : (u - v) idx.2.1 = u idx.2.1 - v idx.2.1 := by simp
    rw [hsub]
    ring
  rw [hterm, Finset.sum_sub_distrib]

lemma map_centeredCorr_diff_gaussian
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u v : EuclideanSpace Real (Fin m)) :
    (muCorr L m rm).map
      (fun omega =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega -
          centeredCorrProcess (L := L) (m := m) (rm := rm) hm A v omega)
      = gaussianReal 0 (vecVarCorr L A (u - v)) := by
  have hSub := M_u_corr_sub (L := L) (m := m) (rm := rm) A u v
  have hEq :
      (fun omega =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega -
          centeredCorrProcess (L := L) (m := m) (rm := rm) hm A v omega) =
      M_u_corr (L := L) (m := m) (rm := rm) A (u - v) := by
    funext omega
    unfold centeredCorrProcess
    have hs := congrArg (fun f => f omega) hSub
    linarith [hs]
  simpa [hEq] using
    map_M_u_corr_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A (u - v)

theorem centeredCorr_isSubGaussian
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real) :
    IsSubGaussianProcess
      (muCorr L m rm)
      (centeredCorrProcess (L := L) (m := m) (rm := rm) hm A)
      (Real.sqrt (invDEff A)) := by
  intro u v l
  have hMap := map_centeredCorr_diff_gaussian
    (L := L) (m := m) (rm := rm) hm hL hrm A u v
  have hmgf := mgf_gaussianReal
    (p := muCorr L m rm)
    (X := fun omega =>
      centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega -
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A v omega)
    (μ := (0 : Real))
    (v := vecVarCorr L A (u - v))
    hMap l
  have hdist : dist u v = norm (u - v) := by
    simp [dist_eq_norm]
  have hInvNonneg : 0 <= invDEff A := by
    unfold invDEff
    exact div_nonneg (rhoSum_nonneg A) (by positivity)
  have hVar :
      ((vecVarCorr L A (u - v) : NNReal) : Real) =
        (dist u v) ^ 2 * invDEff A := by
    simp [vecVarCorr, invDEff, hdist]
    ring
  have hSqrtSq : (Real.sqrt (invDEff A)) ^ 2 = invDEff A := by
    exact Real.sq_sqrt hInvNonneg
  calc
    (muCorr L m rm)[fun omega =>
      Real.exp
        (l *
          (centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega -
            centeredCorrProcess (L := L) (m := m) (rm := rm) hm A v omega))]
        = Real.exp (0 * l + ((vecVarCorr L A (u - v) : NNReal) : Real) * l ^ 2 / 2) := by
            simpa [mgf] using hmgf
    _ = Real.exp (l ^ 2 * ((dist u v) ^ 2 * invDEff A) / 2) := by
          rw [hVar]
          ring_nf
    _ = Real.exp (l ^ 2 * (Real.sqrt (invDEff A)) ^ 2 * (dist u v) ^ 2 / 2) := by
          rw [hSqrtSq]
          ring_nf
    _ ≤ Real.exp (l ^ 2 * (Real.sqrt (invDEff A)) ^ 2 * (dist u v) ^ 2 / 2) := by
          exact le_rfl

lemma measurable_centeredCorr
    {L m rm : Nat} (hm : 0 < m)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    Measurable (centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u) := by
  unfold centeredCorrProcess
  exact (measurable_M_u_corr (L := L) (m := m) (rm := rm) A u).sub
    (measurable_M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm))

lemma integrable_exp_centeredCorr_increment
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u v : EuclideanSpace Real (Fin m))
    (l : Real) :
    Integrable
      (fun omega =>
        Real.exp
          (l *
            (centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega -
              centeredCorrProcess (L := L) (m := m) (rm := rm) hm A v omega)))
      (muCorr L m rm) := by
  let dFn : OmegaCorr L m rm → Real :=
    fun omega =>
      centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega -
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A v omega
  have hMap :
      (muCorr L m rm).map dFn = gaussianReal 0 (vecVarCorr L A (u - v)) :=
    map_centeredCorr_diff_gaussian (L := L) (m := m) (rm := rm) hm hL hrm A u v
  have hMeas : AEMeasurable dFn (muCorr L m rm) :=
    aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hIntMap :
      Integrable (fun x : Real => Real.exp (l * x)) ((muCorr L m rm).map dFn) := by
    simpa [hMap] using
      (integrable_exp_mul_gaussianReal (μ := (0 : Real)) (v := vecVarCorr L A (u - v)) l)
  have hComp := (integrable_map_measure hIntMap.aestronglyMeasurable hMeas).mp hIntMap
  simpa [dFn, Function.comp] using hComp

lemma continuous_centeredCorr_on_sphereSet
    {L m rm : Nat}
    (hm : 0 < m)
    (A : Fin L -> Fin L -> Real)
    (omega : OmegaCorr L m rm) :
    Continuous
      (fun t : sphereSet m =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t.1 omega) := by
  have hContM : Continuous
      (fun u : EuclideanSpace Real (Fin m) =>
        M_u_corr (L := L) (m := m) (rm := rm) A u omega) := by
    unfold M_u_corr
    refine continuous_finset_sum _ ?_
    intro idx hidx
    have hcoord :
        Continuous (fun u : EuclideanSpace Real (Fin m) => u idx.2.1) := by
      simpa using (PiLp.continuous_apply 2 (fun _ : Fin m => Real) idx.2.1)
    have hscaled :
        Continuous
          (fun u : EuclideanSpace Real (Fin m) =>
            (corrScale L rm * sumACol A idx.1 * aCoord omega idx.2.2 *
              latentCoord omega idx.1 idx.2.1 idx.2.2) * u idx.2.1) :=
      (continuous_const.mul hcoord)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hContCentered : Continuous
      (fun u : EuclideanSpace Real (Fin m) =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u omega) := by
    unfold centeredCorrProcess
    exact hContM.sub continuous_const
  exact hContCentered.comp continuous_subtype_val

theorem corr_sphere_expected_sup_bound_entropy
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (hRhoPos : 0 < rhoSum A)
    (hfinite : entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤) :
    integral (muCorr L m rm)
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega)))
      ≤ (12 * Real.sqrt 2) * Real.sqrt (invDEff A) * entropyIntegral (sphereSet m) 2 := by
  haveI : IsProbabilityMeasure (muCorr L m rm) := by
    unfold muCorr muLatent muSharedZ gaussianPi
    infer_instance
  have hsg := centeredCorr_isSubGaussian (L := L) (m := m) (rm := rm) hm hL hrm A
  have hs : TotallyBounded (sphereSet m) := by
    unfold sphereSet
    exact (isCompact_sphere (0 : EuclideanSpace Real (Fin m)) (1 : Real)).totallyBounded
  have hInvPos : 0 < invDEff A := by
    unfold invDEff
    have hDen : 0 < (L : Real) ^ 3 := by positivity
    exact div_pos hRhoPos hDen
  have hsigma : 0 < Real.sqrt (invDEff A) := Real.sqrt_pos.mpr hInvPos
  have hdiam : Metric.diam (sphereSet m) ≤ 2 := sphere_diam_le_two m
  have ht0mem : sphereBaseVec m hm ∈ sphereSet m := sphereBaseVec_mem_sphereSet m hm
  have hcenter :
      ∀ omega,
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A (sphereBaseVec m hm) omega = 0 := by
    intro omega
    unfold centeredCorrProcess
    ring
  have hMeas :
      ∀ t : EuclideanSpace Real (Fin m),
        Measurable (centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t) := by
    intro t
    exact measurable_centeredCorr (L := L) (m := m) (rm := rm) hm A t
  have hIntExp :
      ∀ t s : EuclideanSpace Real (Fin m), ∀ l : Real,
        Integrable
          (fun omega =>
            Real.exp
              (l *
                (centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega -
                  centeredCorrProcess (L := L) (m := m) (rm := rm) hm A s omega)))
          (muCorr L m rm) := by
    intro t s l
    exact integrable_exp_centeredCorr_increment
      (L := L) (m := m) (rm := rm) hm hL hrm A t s l
  have hCont :
      ∀ omega,
        Continuous
          (fun t : sphereSet m =>
            centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t.1 omega) := by
    intro omega
    exact continuous_centeredCorr_on_sphereSet (L := L) (m := m) (rm := rm) hm A omega
  have hD : (0 : Real) < 2 := by norm_num
  simpa [sphereSet] using
    (dudley
      (μ := muCorr L m rm)
      (X := centeredCorrProcess (L := L) (m := m) (rm := rm) hm A)
      (σ := Real.sqrt (invDEff A))
      hsigma hsg hs hD hdiam
      (sphereBaseVec m hm) ht0mem hcenter hMeas hIntExp hfinite hCont)

theorem corr_sphere_expected_sup_bound_assuming_entropy
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (hRhoPos : 0 < rhoSum A)
    (hfinite : entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤)
    (hEntropy : entropyIntegral (sphereSet m) 2 ≤ 4 * Real.sqrt (m : Real)) :
    integral (muCorr L m rm)
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega)))
      ≤ (48 * Real.sqrt 2) * Real.sqrt (invDEff A) * Real.sqrt (m : Real) := by
  have hBase := corr_sphere_expected_sup_bound_entropy
    (L := L) (m := m) (rm := rm) hm hL hrm A hRhoPos hfinite
  have hScaleNonneg : 0 ≤ (12 * Real.sqrt 2) * Real.sqrt (invDEff A) := by
    positivity
  calc
    integral (muCorr L m rm)
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega)))
      ≤ (12 * Real.sqrt 2) * Real.sqrt (invDEff A) * entropyIntegral (sphereSet m) 2 := hBase
    _ ≤ (12 * Real.sqrt 2) * Real.sqrt (invDEff A) * (4 * Real.sqrt (m : Real)) := by
          gcongr
    _ = (48 * Real.sqrt 2) * Real.sqrt (invDEff A) * Real.sqrt (m : Real) := by
          ring

lemma centeredCorr_biSup_eq_centeredSphereSup
    {L m rm : Nat}
    (hm : 0 < m) (A : Fin L -> Fin L -> Real)
    (omega : OmegaCorr L m rm) :
    (iSup (fun t : EuclideanSpace Real (Fin m) =>
      iSup (fun _ : t ∈ sphereSet m =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega))) =
    iSup (fun u : Sphere m =>
      M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
        M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega) := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  haveI : Nonempty (SphereSetSub m) :=
    Nonempty.intro (sphereToSphereSetSub m (sphereBasePoint m hm))
  have hsne : (sphereSet m).Nonempty :=
    ⟨sphereBaseVec m hm, sphereBaseVec_mem_sphereSet m hm⟩
  have hzero :
      ∃ t ∈ sphereSet m,
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega = 0 := by
    refine ⟨sphereBaseVec m hm, sphereBaseVec_mem_sphereSet m hm, by
      unfold centeredCorrProcess
      ring⟩
  have hSubtype :
      (iSup (fun t : EuclideanSpace Real (Fin m) =>
        iSup (fun _ : t ∈ sphereSet m =>
          centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega))) =
        iSup (fun t : SphereSetSub m =>
          centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t.1 omega) := by
    simpa [SphereSetSub] using
      (biSup_eq_iSup_subtype_real
        (s := sphereSet m)
        (f := fun t => centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega)
        hsne hzero)
  have hEquiv :
      iSup (fun t : SphereSetSub m =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t.1 omega) =
      iSup (fun u : Sphere m =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u.1 omega) := by
    let e : SphereSetSub m ≃ Sphere m := (sphereEquivSphereSetSub m).symm
    exact e.iSup_congr (by intro t; rfl)
  have hPoint :
      ∀ u : Sphere m,
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u.1 omega =
          M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega := by
    intro u
    rfl
  have hSphere :
      iSup (fun u : Sphere m =>
        centeredCorrProcess (L := L) (m := m) (rm := rm) hm A u.1 omega) =
      iSup (fun u : Sphere m =>
        M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
          M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega) := by
    refine iSup_congr ?_
    intro u
    exact hPoint u
  exact hSubtype.trans (hEquiv.trans hSphere)

lemma sqrt_invDEff_eq_inv_sqrt_DEff
    {L : Nat} (A : Fin L -> Fin L -> Real) (hL : 0 < L) (hRhoPos : 0 < rhoSum A) :
    Real.sqrt (invDEff A) = 1 / Real.sqrt (D_eff A) := by
  have hRho0 : rhoSum A ≠ 0 := ne_of_gt hRhoPos
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hInv :
      invDEff A = 1 / D_eff A := by
    unfold invDEff D_eff
    field_simp [hRho0, hL0]
  calc
    Real.sqrt (invDEff A) = Real.sqrt ((D_eff A)⁻¹) := by simpa [hInv, one_div]
    _ = (Real.sqrt (D_eff A))⁻¹ := by rw [Real.sqrt_inv]
    _ = 1 / Real.sqrt (D_eff A) := by simp [one_div]

theorem corr_sphere_expected_sup_bound
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (hRhoPos : 0 < rhoSum A) :
    integral (muCorr L m rm)
      (fun omega =>
        iSup (fun u : Sphere m =>
          M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega))
      ≤ (48 * Real.sqrt 2) * (Real.sqrt (m : Real) / Real.sqrt (D_eff A)) := by
  have hfinite : entropyIntegralENNReal (sphereSet m) 2 ≠ ⊤ :=
    entropyIntegralENNReal_sphere_ne_top m hm
  have hEntropy : entropyIntegral (sphereSet m) 2 ≤ 4 * Real.sqrt (m : Real) :=
    entropyIntegral_sphere_le m hm
  have hBase := corr_sphere_expected_sup_bound_assuming_entropy
    (L := L) (m := m) (rm := rm) hm hL hrm A hRhoPos hfinite hEntropy
  have hEq :
      (fun omega =>
        iSup (fun t : EuclideanSpace Real (Fin m) =>
          iSup (fun _ : t ∈ sphereSet m =>
            centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega))) =
      (fun omega =>
        iSup (fun u : Sphere m =>
          M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega)) := by
    funext omega
    exact centeredCorr_biSup_eq_centeredSphereSup (L := L) (m := m) (rm := rm) hm A omega
  have hInv :
      Real.sqrt (invDEff A) = 1 / Real.sqrt (D_eff A) :=
    sqrt_invDEff_eq_inv_sqrt_DEff A hL hRhoPos
  calc
    integral (muCorr L m rm)
      (fun omega =>
        iSup (fun u : Sphere m =>
          M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega))
      = integral (muCorr L m rm)
          (fun omega =>
            iSup (fun t : EuclideanSpace Real (Fin m) =>
              iSup (fun _ : t ∈ sphereSet m =>
                centeredCorrProcess (L := L) (m := m) (rm := rm) hm A t omega))) := by
            simpa [hEq] using rfl
    _ ≤ (48 * Real.sqrt 2) * Real.sqrt (invDEff A) * Real.sqrt (m : Real) := hBase
    _ = (48 * Real.sqrt 2) * (Real.sqrt (m : Real) / Real.sqrt (D_eff A)) := by
          rw [hInv]
          ring

theorem corr_sphere_expected_sup_bound_layerAvg
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (hRhoPos : 0 < rhoSum A) :
    integral (muCorr L m rm)
      (fun omega =>
        iSup (fun u : Sphere m =>
          M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega))
      ≤ (48 * Real.sqrt 2) * (Real.sqrt (m : Real) / Real.sqrt (D_eff A)) := by
  have hBase := corr_sphere_expected_sup_bound
    (L := L) (m := m) (rm := rm) hm hL hrm A hRhoPos
  have hEq :
      (fun omega =>
        iSup (fun u : Sphere m =>
          M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega)) =
      (fun omega =>
        iSup (fun u : Sphere m =>
          M_u_corr (L := L) (m := m) (rm := rm) A u.1 omega -
            M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm) omega)) := by
    funext omega
    refine iSup_congr ?_
    intro u
    simp [M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A u.1,
      M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A (sphereBaseVec m hm)]
  simpa [hEq] using hBase

lemma bddAbove_XCorr_range
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (omega : OmegaCorr L m rm) :
    BddAbove (Set.range (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)) := by
  refine ⟨Real.sqrt (Finset.univ.sum (fun i : Fin m => (Wcorr (L := L) (m := m) (rm := rm) A omega i) ^ 2)), ?_⟩
  intro y hy
  rcases hy with ⟨u, hu⟩
  rw [← hu]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
    (fun i => u.1 i) (fun i => Wcorr (L := L) (m := m) (rm := rm) A omega i)
  have huSqrt : Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) = 1 := by
    calc
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2))
          = norm u.1 := by
              symm
              simpa using (EuclideanSpace.norm_eq u.1)
      _ = 1 := u.2
  calc
    XCorr (L := L) (m := m) (rm := rm) A u omega
        = Finset.univ.sum (fun i : Fin m => u.1 i * Wcorr (L := L) (m := m) (rm := rm) A omega i) := by
            rfl
    _ <= Real.sqrt (Finset.univ.sum (fun i : Fin m => (u.1 i) ^ 2)) *
          Real.sqrt (Finset.univ.sum
            (fun i : Fin m => (Wcorr (L := L) (m := m) (rm := rm) A omega i) ^ 2)) := by
          simpa using hcs
    _ = Real.sqrt (Finset.univ.sum
          (fun i : Fin m => (Wcorr (L := L) (m := m) (rm := rm) A omega i) ^ 2)) := by
          rw [huSqrt, one_mul]

lemma supXCorr_le_sum_absWcorr
    {L m rm : Nat}
    (hm : 0 < m)
    (A : Fin L -> Fin L -> Real)
    (omega : OmegaCorr L m rm) :
    iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega) <=
      ∑ i : Fin m, |Wcorr (L := L) (m := m) (rm := rm) A omega i| := by
  haveI : Nonempty (Sphere m) := Nonempty.intro (sphereBasePoint m hm)
  have hBdd : BddAbove (Set.range (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)) :=
    bddAbove_XCorr_range (L := L) (m := m) (rm := rm) A omega
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
    XCorr (L := L) (m := m) (rm := rm) A u omega
        <= |XCorr (L := L) (m := m) (rm := rm) A u omega| := le_abs_self _
    _ = |∑ i : Fin m, u.1 i * Wcorr (L := L) (m := m) (rm := rm) A omega i| := by rfl
    _ <= ∑ i : Fin m, |u.1 i * Wcorr (L := L) (m := m) (rm := rm) A omega i| := by
          simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin m =>
            u.1 i * Wcorr (L := L) (m := m) (rm := rm) A omega i) Finset.univ)
    _ = ∑ i : Fin m, |u.1 i| * |Wcorr (L := L) (m := m) (rm := rm) A omega i| := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact abs_mul (u.1 i) (Wcorr (L := L) (m := m) (rm := rm) A omega i)
    _ <= ∑ i : Fin m, 1 * |Wcorr (L := L) (m := m) (rm := rm) A omega i| := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg _)
    _ = ∑ i : Fin m, |Wcorr (L := L) (m := m) (rm := rm) A omega i| := by
          simp

lemma sphere_corr_sup_event_subset_union_coords
    {L m rm : Nat}
    (hm : 0 < m)
    (A : Fin L -> Fin L -> Real)
    (t : Real) (ht : 0 < t) :
    Set.Subset
      {omega : OmegaCorr L m rm |
        t <= iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)}
      (Set.iUnion (fun i : Fin m =>
        {omega : OmegaCorr L m rm |
          t / (m : Real) <= |Wcorr (L := L) (m := m) (rm := rm) A omega i|})) := by
  intro omega hsup
  by_contra hnot
  have hall : ∀ i : Fin m,
      |Wcorr (L := L) (m := m) (rm := rm) A omega i| < t / (m : Real) := by
    intro i
    exact lt_of_not_ge (by
      intro hi
      exact hnot (Set.mem_iUnion.2 ⟨i, hi⟩))
  have hsum_lt :
      Finset.univ.sum
          (fun i : Fin m => |Wcorr (L := L) (m := m) (rm := rm) A omega i|)
        <
      Finset.univ.sum (fun _ : Fin m => t / (m : Real)) := by
    classical
    have hlt : ∃ i ∈ (Finset.univ : Finset (Fin m)),
        |Wcorr (L := L) (m := m) (rm := rm) A omega i| < t / (m : Real) := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      exact ⟨Classical.choice ‹Nonempty (Fin m)›, Finset.mem_univ _, hall _⟩
    exact Finset.sum_lt_sum (fun i _ => le_of_lt (hall i)) hlt
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hsum_const :
      Finset.univ.sum (fun _ : Fin m => t / (m : Real)) = t := by
    calc
      Finset.univ.sum (fun _ : Fin m => t / (m : Real))
          = (Fintype.card (Fin m) : Real) * (t / (m : Real)) := by simp
      _ = (m : Real) * (t / (m : Real)) := by simp
      _ = t := by field_simp [hm0]
  have hsum_abs_lt :
      Finset.univ.sum (fun i : Fin m => |Wcorr (L := L) (m := m) (rm := rm) A omega i|) < t := by
    simpa [hsum_const] using hsum_lt
  have hsup_le :
      iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)
        <= Finset.univ.sum
            (fun i : Fin m => |Wcorr (L := L) (m := m) (rm := rm) A omega i|) := by
    exact supXCorr_le_sum_absWcorr (L := L) (m := m) (rm := rm) hm A omega
  have hsup_lt :
      iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega) < t :=
    lt_of_le_of_lt hsup_le hsum_abs_lt
  exact (not_le_of_gt hsup_lt) hsup

lemma Wcorr_coord_eq_M_u_corr_single
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (i : Fin m) :
    (fun omega : OmegaCorr L m rm => Wcorr (L := L) (m := m) (rm := rm) A omega i) =
      M_u_corr (L := L) (m := m) (rm := rm) A (EuclideanSpace.single i (1 : Real)) := by
  funext omega
  unfold Wcorr M_u_corr
  simp [Fintype.sum_prod_type, EuclideanSpace.single_apply, mul_left_comm, mul_comm]

theorem corr_sphere_highProb_bound
    {L m rm : Nat}
    (hm : 0 < m) (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (hRhoPos : 0 < rhoSum A)
    (t : Real) (ht : 0 < t) :
    ((muCorr L m rm) {omega |
      t <= iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)}).toReal <=
      2 * (m : Real) * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2) := by
  haveI : IsProbabilityMeasure (muCorr L m rm) := by
    unfold muCorr muLatent muSharedZ gaussianPi
    infer_instance
  let E : Set (OmegaCorr L m rm) :=
    {omega | t <= iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)}
  let B : Fin m -> Set (OmegaCorr L m rm) := fun i =>
    {omega | t / (m : Real) <= |Wcorr (L := L) (m := m) (rm := rm) A omega i|}
  have hE_subset_union : E ⊆ Set.iUnion B := by
    simpa [E, B] using
      sphere_corr_sup_event_subset_union_coords (L := L) (m := m) (rm := rm) hm A t ht
  have hUnion :
      (muCorr L m rm) E <= (muCorr L m rm) (Set.iUnion B) := measure_mono hE_subset_union
  have hUnionSum :
      (muCorr L m rm) (Set.iUnion B) <= ∑ i : Fin m, (muCorr L m rm) (B i) := by
    calc
      (muCorr L m rm) (Set.iUnion B) <= ∑' i : Fin m, (muCorr L m rm) (B i) := measure_iUnion_le B
      _ = ∑ i : Fin m, (muCorr L m rm) (B i) := by simp [tsum_fintype]
  have hsum_ne_top : (∑ i : Fin m, (muCorr L m rm) (B i)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 (fun i hi => measure_ne_top _ _)
  have hE_toReal :
      ((muCorr L m rm) E).toReal <= (∑ i : Fin m, (muCorr L m rm) (B i)).toReal := by
    exact ENNReal.toReal_mono hsum_ne_top (hUnion.trans hUnionSum)
  have hsum_toReal :
      (∑ i : Fin m, (muCorr L m rm) (B i)).toReal =
        ∑ i : Fin m, ((muCorr L m rm) (B i)).toReal := by
    simpa using
      (ENNReal.toReal_sum (s := (Finset.univ : Finset (Fin m)))
        (f := fun i : Fin m => (muCorr L m rm) (B i))
        (fun i hi => measure_ne_top _ _))
  have hcoord :
      ∀ i : Fin m,
        ((muCorr L m rm) (B i)).toReal <=
          2 * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2) := by
    intro i
    have hu : norm (EuclideanSpace.single i (1 : Real)) = 1 := by
      simp [EuclideanSpace.norm_single]
    have htScaled : 0 < t / (m : Real) := by
      have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
      positivity
    have htail := corr_scalar_tail (L := L) (m := m) (rm := rm) hL hrm
      A (EuclideanSpace.single i (1 : Real)) hu hRhoPos (t / (m : Real)) htScaled
    simpa [B, (Wcorr_coord_eq_M_u_corr_single (L := L) (m := m) (rm := rm) A i).symm, ge_iff_le] using htail
  have hsum_coord :
      (∑ i : Fin m, ((muCorr L m rm) (B i)).toReal) <=
        ∑ i : Fin m, (2 * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2)) := by
    exact Finset.sum_le_sum (fun i hi => hcoord i)
  have hsum_const :
      (∑ i : Fin m, (2 * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2)))
        = 2 * (m : Real) * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2) := by
    simp [Finset.card_univ, mul_assoc, mul_comm]
  calc
    ((muCorr L m rm) {omega |
      t <= iSup (fun u : Sphere m => XCorr (L := L) (m := m) (rm := rm) A u omega)}).toReal
        = ((muCorr L m rm) E).toReal := by rfl
    _ <= (∑ i : Fin m, (muCorr L m rm) (B i)).toReal := hE_toReal
    _ = ∑ i : Fin m, ((muCorr L m rm) (B i)).toReal := hsum_toReal
    _ <= ∑ i : Fin m, (2 * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2)) := hsum_coord
    _ = 2 * (m : Real) * Real.exp (-(t / (m : Real)) ^ 2 * (D_eff A) / 2) := hsum_const

end

end Correlated
end NNGPResNet
end LeanSlt
