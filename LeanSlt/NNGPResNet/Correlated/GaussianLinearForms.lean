import LeanSlt.NNGPResNet.Correlated.Defs
import LeanSlt.NNGPResNet.GaussianLinearForms

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet
namespace Correlated

noncomputable section

def coeffCorrWithSign {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (zv : SharedZSpace rm)
    (idx : LatentIdx L m rm) : Real :=
  corrScale L rm * u idx.2.1 * sumACol A idx.1 * signAct (zv idx.2.2)

def linearProbeLatent {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (zv : SharedZSpace rm)
    (g : LatentSpace L m rm) : Real :=
  Finset.univ.sum (fun idx : LatentIdx L m rm => coeffCorrWithSign A u zv idx * g idx)

lemma M_u_corr_eq_linearProbeLatent {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    M_u_corr A u = fun omega : OmegaCorr L m rm => linearProbeLatent A u omega.2 omega.1 := by
  funext omega
  unfold M_u_corr linearProbeLatent coeffCorrWithSign aCoord zCoord latentCoord
  rfl

lemma measurable_linearProbeLatent
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (zv : SharedZSpace rm) :
    Measurable (linearProbeLatent A u zv) := by
  unfold linearProbeLatent
  refine Finset.measurable_sum (s := (Finset.univ : Finset (LatentIdx L m rm))) ?_
  intro idx hidx
  exact ((measurable_const_mul (coeffCorrWithSign A u zv idx)).comp (measurable_pi_apply idx))

lemma measurable_M_u_corr
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    Measurable (M_u_corr (L := L) (m := m) (rm := rm) A u) := by
  unfold M_u_corr
  refine Finset.measurable_sum (s := (Finset.univ : Finset (LatentIdx L m rm))) ?_
  intro idx hidx
  have hLat : Measurable (fun omega : OmegaCorr L m rm =>
      latentCoord omega idx.1 idx.2.1 idx.2.2) := by
    unfold latentCoord
    exact (measurable_pi_apply (idx.1, (idx.2.1, idx.2.2))).comp measurable_fst
  have hA : Measurable (fun omega : OmegaCorr L m rm => aCoord omega idx.2.2) := by
    unfold aCoord zCoord
    exact measurable_signAct.comp ((measurable_pi_apply idx.2.2).comp measurable_snd)
  have hMul : Measurable (fun omega : OmegaCorr L m rm =>
      aCoord omega idx.2.2 * latentCoord omega idx.1 idx.2.1 idx.2.2) :=
    hA.mul hLat
  have hScaled : Measurable (fun omega : OmegaCorr L m rm =>
      (corrScale L rm * u idx.2.1 * sumACol A idx.1) *
        (aCoord omega idx.2.2 * latentCoord omega idx.1 idx.2.1 idx.2.2)) :=
    (measurable_const_mul (corrScale L rm * u idx.2.1 * sumACol A idx.1)).comp hMul
  simpa [mul_assoc, mul_left_comm, mul_comm] using hScaled

lemma map_linearProbeLatent_gaussian
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (zv : SharedZSpace rm) :
    (muLatent L m rm).map (linearProbeLatent A u zv) =
      gaussianReal 0
        (Finset.univ.sum (fun idx : LatentIdx L m rm => sqNN (coeffCorrWithSign A u zv idx))) := by
  simpa [muLatent, linearProbeLatent, coeffCorrWithSign]
    using map_linear_sum_gaussianPi_eq_gaussian (a := coeffCorrWithSign A u zv)

lemma weighted_sum_sq_split
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    Finset.univ.sum (fun idx : LatentIdx L m rm =>
      (u idx.2.1) ^ 2 * (sumACol A idx.1) ^ 2) =
      (rm : Real) *
        (Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2)) *
        (Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) := by
  calc
    Finset.univ.sum (fun idx : LatentIdx L m rm =>
      (u idx.2.1) ^ 2 * (sumACol A idx.1) ^ 2)
        = Finset.univ.sum (fun t : Fin L =>
            Finset.univ.sum (fun i : Fin m =>
              Finset.univ.sum (fun j : Fin rm => (u i) ^ 2 * (sumACol A t) ^ 2))) := by
              simp [Fintype.sum_prod_type]
    _ = Finset.univ.sum (fun t : Fin L =>
          Finset.univ.sum (fun i : Fin m =>
            (rm : Real) * ((u i) ^ 2 * (sumACol A t) ^ 2))) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp
    _ = Finset.univ.sum (fun t : Fin L =>
          (rm : Real) * ((sumACol A t) ^ 2 * Finset.univ.sum (fun i : Fin m => (u i) ^ 2))) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            calc
              Finset.univ.sum (fun i : Fin m => (rm : Real) * ((u i) ^ 2 * (sumACol A t) ^ 2))
                  = (rm : Real) * Finset.univ.sum (fun i : Fin m => (u i) ^ 2 * (sumACol A t) ^ 2) := by
                      rw [Finset.mul_sum]
              _ = (rm : Real) * ((sumACol A t) ^ 2 * Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) := by
                    congr 1
                    calc
                      Finset.univ.sum (fun i : Fin m => (u i) ^ 2 * (sumACol A t) ^ 2)
                          = (Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) * (sumACol A t) ^ 2 := by
                              rw [Finset.sum_mul]
                      _ = (sumACol A t) ^ 2 * Finset.univ.sum (fun i : Fin m => (u i) ^ 2) := by
                            ring
    _ = (rm : Real) * (Finset.univ.sum
          (fun t : Fin L => (sumACol A t) ^ 2 * Finset.univ.sum (fun i : Fin m => (u i) ^ 2))) := by
            symm
            rw [Finset.mul_sum]
    _ = (rm : Real) * (Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2)) *
          (Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) := by
            have hSum :
                (Finset.univ.sum
                  (fun t : Fin L =>
                    (sumACol A t) ^ 2 * Finset.univ.sum (fun i : Fin m => (u i) ^ 2)))
                  = (Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2)) *
                    (Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) := by
                      rw [Finset.sum_mul]
            rw [hSum]
            ring

lemma coeff_variance_eq_norm_sq_rhoSum
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (zv : SharedZSpace rm) :
    (Finset.univ.sum (fun idx : LatentIdx L m rm => sqNN (coeffCorrWithSign A u zv idx)) : Real)
      = norm u ^ 2 * rhoSum A / (L : Real) ^ 3 := by
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hrm0 : (rm : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hrm)
  have hsqrtL0 : Real.sqrt (L : Real) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hL))
  have hsqrtrm0 : Real.sqrt (rm : Real) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hrm))
  have hScale : (corrScale L rm) ^ 2 * (rm : Real) = 1 / (L : Real) ^ 3 := by
    have hLsq : (Real.sqrt (L : Real)) ^ 2 = (L : Real) := by
      nlinarith [Real.sq_sqrt (show (0 : Real) <= (L : Real) by positivity)]
    have hrmsq : (Real.sqrt (rm : Real)) ^ 2 = (rm : Real) := by
      nlinarith [Real.sq_sqrt (show (0 : Real) <= (rm : Real) by positivity)]
    unfold corrScale
    field_simp [hL0, hrm0, hsqrtL0, hsqrtrm0]
    rw [hLsq, hrmsq]
  calc
    (Finset.univ.sum (fun idx : LatentIdx L m rm => sqNN (coeffCorrWithSign A u zv idx)) : Real)
        = Finset.univ.sum (fun idx : LatentIdx L m rm => (coeffCorrWithSign A u zv idx) ^ 2) := by
            simp [sqNN]
    _ = Finset.univ.sum (fun idx : LatentIdx L m rm =>
          (corrScale L rm) ^ 2 * (u idx.2.1) ^ 2 * (sumACol A idx.1) ^ 2 *
            (signAct (zv idx.2.2)) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro idx hidx
          unfold coeffCorrWithSign
          ring
    _ = Finset.univ.sum (fun idx : LatentIdx L m rm =>
          (corrScale L rm) ^ 2 * (u idx.2.1) ^ 2 * (sumACol A idx.1) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro idx hidx
          simp [signAct_sq]
    _ = (corrScale L rm) ^ 2 *
          Finset.univ.sum (fun idx : LatentIdx L m rm => (u idx.2.1) ^ 2 * (sumACol A idx.1) ^ 2) := by
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro idx hidx
          ring
    _ = (corrScale L rm) ^ 2 *
          ((rm : Real) *
            (Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2)) *
            (Finset.univ.sum (fun i : Fin m => (u i) ^ 2))) := by
          rw [weighted_sum_sq_split]
    _ = ((corrScale L rm) ^ 2 * (rm : Real)) *
          (Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2)) *
          (Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) := by
          ring
    _ = (1 / (L : Real) ^ 3) *
          (Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2)) *
          (Finset.univ.sum (fun i : Fin m => (u i) ^ 2)) := by
          rw [hScale]
    _ = (1 / (L : Real) ^ 3) * (rhoSum A) * (norm u ^ 2) := by
          rw [rhoSum_eq_sum_sq_colSums, sum_sq_eq_norm_sq]
    _ = norm u ^ 2 * rhoSum A / (L : Real) ^ 3 := by
          ring

def vecVarCorr (L : Nat) {m : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) : NNReal :=
  Subtype.mk (norm u ^ 2 * rhoSum A / (L : Real) ^ 3) (by
    have hNum : 0 <= norm u ^ 2 * rhoSum A := by
      exact mul_nonneg (sq_nonneg (norm u)) (rhoSum_nonneg A)
    have hDen : 0 <= (L : Real) ^ 3 := by positivity
    exact div_nonneg hNum hDen)

lemma map_linearProbeLatent_gaussian_normSq
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (zv : SharedZSpace rm) :
    (muLatent L m rm).map (linearProbeLatent A u zv) =
      gaussianReal 0 (vecVarCorr L A u) := by
  have hMap := map_linearProbeLatent_gaussian A u zv
  have hVar :
      (Finset.univ.sum (fun idx : LatentIdx L m rm => sqNN (coeffCorrWithSign A u zv idx)) : Real)
        = norm u ^ 2 * rhoSum A / (L : Real) ^ 3 :=
    coeff_variance_eq_norm_sq_rhoSum hL hrm A u zv
  calc
    (muLatent L m rm).map (linearProbeLatent A u zv)
        = gaussianReal 0
            (Finset.univ.sum (fun idx : LatentIdx L m rm => sqNN (coeffCorrWithSign A u zv idx))) := hMap
    _ = gaussianReal 0 (vecVarCorr L A u) := by
          apply congrArg (gaussianReal 0)
          apply Subtype.ext
          simpa [vecVarCorr] using hVar

theorem map_M_u_corr_gaussian_any
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    (muCorr L m rm).map (M_u_corr (L := L) (m := m) (rm := rm) A u) = gaussianReal 0 (vecVarCorr L A u) := by
  haveI : SFinite (muSharedZ rm) := by
    unfold muSharedZ gaussianPi
    infer_instance
  haveI : SFinite (muLatent L m rm) := by
    unfold muLatent gaussianPi
    infer_instance
  have hMeasM : Measurable (M_u_corr (L := L) (m := m) (rm := rm) A u) :=
    measurable_M_u_corr (L := L) (m := m) (rm := rm) A u
  ext s hs
  let pre := Set.preimage (M_u_corr (L := L) (m := m) (rm := rm) A u) s
  have hPre : MeasurableSet pre := hMeasM hs
  calc
    ((muCorr L m rm).map (M_u_corr (L := L) (m := m) (rm := rm) A u)) s = (muCorr L m rm) pre := by
      simpa [pre] using Measure.map_apply hMeasM hs
    _ = lintegral (muSharedZ rm) (fun zv : SharedZSpace rm =>
          (muLatent L m rm) (Set.preimage (fun g : LatentSpace L m rm => (g, zv)) pre)) := by
          unfold muCorr
          simpa [pre] using Measure.prod_apply_symm hPre
    _ = lintegral (muSharedZ rm) (fun _ : SharedZSpace rm => (gaussianReal 0 (vecVarCorr L A u)) s) := by
          refine lintegral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro zv
          have hMapZ := map_linearProbeLatent_gaussian_normSq hL hrm A u zv
          have hMeasZ : Measurable (linearProbeLatent A u zv) := measurable_linearProbeLatent A u zv
          have hSetEq :
              Set.preimage (fun g : LatentSpace L m rm => (g, zv)) pre =
                Set.preimage (linearProbeLatent A u zv) s := by
            ext g
            simp [pre, M_u_corr_eq_linearProbeLatent]
          calc
            (muLatent L m rm) (Set.preimage (fun g : LatentSpace L m rm => (g, zv)) pre)
                = (muLatent L m rm) (Set.preimage (linearProbeLatent A u zv) s) := by
                    rw [hSetEq]
            _ = ((muLatent L m rm).map (linearProbeLatent A u zv)) s := by
                  symm
                  exact Measure.map_apply hMeasZ hs
            _ = (gaussianReal 0 (vecVarCorr L A u)) s := by
                  simpa using congrArg (fun nu => nu s) hMapZ
    _ = (gaussianReal 0 (vecVarCorr L A u)) s := by
          haveI : IsProbabilityMeasure (muSharedZ rm) := by
            unfold muSharedZ gaussianPi
            infer_instance
          simp

def Arow {L : Nat} (A : Fin L -> Fin L -> Real) (ell : Fin L) : Fin L -> Fin L -> Real :=
  fun _ t => A ell t

def ArowPair {L : Nat} (A : Fin L -> Fin L -> Real)
    (ell k : Fin L) : Fin L -> Fin L -> Real :=
  fun _ t => A ell t + A k t

lemma sumACol_Arow
    {L : Nat} (A : Fin L -> Fin L -> Real) (ell t : Fin L) :
    sumACol (Arow A ell) t = (L : Real) * A ell t := by
  unfold sumACol Arow
  simp [Finset.sum_const, nsmul_eq_mul]

lemma sumACol_ArowPair
    {L : Nat} (A : Fin L -> Fin L -> Real) (ell k t : Fin L) :
    sumACol (ArowPair A ell k) t = (L : Real) * (A ell t + A k t) := by
  unfold sumACol ArowPair
  simp [Finset.sum_const, nsmul_eq_mul, mul_add]

lemma rhoSum_Arow
    {L : Nat} (A : Fin L -> Fin L -> Real) (ell : Fin L) :
    rhoSum (Arow A ell) = (L : Real) ^ 2 * rho A ell ell := by
  calc
    rhoSum (Arow A ell)
        = Finset.univ.sum (fun t : Fin L => (sumACol (Arow A ell) t) ^ 2) := rhoSum_eq_sum_sq_colSums _
    _ = Finset.univ.sum (fun t : Fin L => ((L : Real) * A ell t) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [sumACol_Arow]
    _ = (L : Real) ^ 2 * Finset.univ.sum (fun t : Fin L => (A ell t) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
    _ = (L : Real) ^ 2 * rho A ell ell := by
          unfold rho
          congr 1
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring

lemma rhoSum_ArowPair
    {L : Nat} (A : Fin L -> Fin L -> Real) (ell k : Fin L) :
    rhoSum (ArowPair A ell k) =
      (L : Real) ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k) := by
  have hQuad :
      Finset.univ.sum (fun t : Fin L => (A ell t + A k t) ^ 2) =
        rho A ell ell + rho A k k + 2 * rho A ell k := by
    have hExpand :
        Finset.univ.sum (fun t : Fin L => (A ell t + A k t) ^ 2) =
          Finset.univ.sum (fun t : Fin L => (A ell t) ^ 2) +
            Finset.univ.sum (fun t : Fin L => (A k t) ^ 2) +
            2 * Finset.univ.sum (fun t : Fin L => A ell t * A k t) := by
      calc
        Finset.univ.sum (fun t : Fin L => (A ell t + A k t) ^ 2)
            = Finset.univ.sum
                (fun t : Fin L => (A ell t) ^ 2 + (A k t) ^ 2 + 2 * (A ell t * A k t)) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  ring
        _ = Finset.univ.sum (fun t : Fin L => (A ell t) ^ 2) +
              Finset.univ.sum (fun t : Fin L => (A k t) ^ 2) +
              2 * Finset.univ.sum (fun t : Fin L => A ell t * A k t) := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                rw [Finset.mul_sum]
    have hEllSq :
        Finset.univ.sum (fun t : Fin L => (A ell t) ^ 2) =
          Finset.univ.sum (fun t : Fin L => A ell t * A ell t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    have hKSq :
        Finset.univ.sum (fun t : Fin L => (A k t) ^ 2) =
          Finset.univ.sum (fun t : Fin L => A k t * A k t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    unfold rho
    calc
      Finset.univ.sum (fun t : Fin L => (A ell t + A k t) ^ 2)
          = Finset.univ.sum (fun t : Fin L => (A ell t) ^ 2) +
              Finset.univ.sum (fun t : Fin L => (A k t) ^ 2) +
              2 * Finset.univ.sum (fun t : Fin L => A ell t * A k t) := hExpand
      _ = Finset.univ.sum (fun t : Fin L => A ell t * A ell t) +
            Finset.univ.sum (fun t : Fin L => A k t * A k t) +
            2 * Finset.univ.sum (fun t : Fin L => A ell t * A k t) := by
              rw [hEllSq, hKSq]
      _ = rho A ell ell + rho A k k + 2 * rho A ell k := by rfl
  calc
    rhoSum (ArowPair A ell k)
        = Finset.univ.sum (fun t : Fin L => (sumACol (ArowPair A ell k) t) ^ 2) := rhoSum_eq_sum_sq_colSums _
    _ = Finset.univ.sum (fun t : Fin L => ((L : Real) * (A ell t + A k t)) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [sumACol_ArowPair]
    _ = (L : Real) ^ 2 * Finset.univ.sum (fun t : Fin L => (A ell t + A k t) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
    _ = (L : Real) ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k) := by rw [hQuad]

lemma gCorr_Arow_eq
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell ell' : Fin L)
    (omega : OmegaCorr L m rm) :
    gCorr (L := L) (m := m) (rm := rm) (Arow A ell) u ell' omega =
      gCorr (L := L) (m := m) (rm := rm) A u ell omega := by
  unfold gCorr deltaHCorr Bcorr Arow
  simp

lemma gCorr_ArowPair_eq
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell k ell' : Fin L)
    (omega : OmegaCorr L m rm) :
    gCorr (L := L) (m := m) (rm := rm) (ArowPair A ell k) u ell' omega =
      gCorr (L := L) (m := m) (rm := rm) A u ell omega +
        gCorr (L := L) (m := m) (rm := rm) A u k omega := by
  unfold gCorr deltaHCorr Bcorr ArowPair
  simp [Finset.sum_add_distrib, add_mul, mul_add, mul_assoc]

lemma gCorr_eq_M_u_corr_Arow
    {L m rm : Nat}
    (hL : 0 < L)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell : Fin L) :
    (fun omega : OmegaCorr L m rm =>
      gCorr (L := L) (m := m) (rm := rm) A u ell omega) =
      M_u_corr (L := L) (m := m) (rm := rm) (Arow A ell) u := by
  funext omega
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hAvg :
      M_u_corr_layerAvg (L := L) (m := m) (rm := rm) (Arow A ell) u omega =
        gCorr (L := L) (m := m) (rm := rm) A u ell omega := by
    unfold M_u_corr_layerAvg
    have hConst :
        (∑ ell' : Fin L, gCorr (L := L) (m := m) (rm := rm) (Arow A ell) u ell' omega) =
          ∑ ell' : Fin L, gCorr (L := L) (m := m) (rm := rm) A u ell omega := by
      refine Finset.sum_congr rfl ?_
      intro ell' hEll'
      exact gCorr_Arow_eq A u ell ell' omega
    rw [hConst, Finset.sum_const, nsmul_eq_mul]
    simp
    field_simp [hL0]
  have hBridge := congrArg (fun f => f omega)
    (M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) (A := Arow A ell) u)
  calc
    gCorr (L := L) (m := m) (rm := rm) A u ell omega
        = M_u_corr_layerAvg (L := L) (m := m) (rm := rm) (Arow A ell) u omega := by
            exact hAvg.symm
    _ = M_u_corr (L := L) (m := m) (rm := rm) (Arow A ell) u omega := hBridge

lemma gCorr_add_eq_M_u_corr_ArowPair
    {L m rm : Nat}
    (hL : 0 < L)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell k : Fin L) :
    (fun omega : OmegaCorr L m rm =>
      gCorr (L := L) (m := m) (rm := rm) A u ell omega +
        gCorr (L := L) (m := m) (rm := rm) A u k omega) =
      M_u_corr (L := L) (m := m) (rm := rm) (ArowPair A ell k) u := by
  funext omega
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hAvg :
      M_u_corr_layerAvg (L := L) (m := m) (rm := rm) (ArowPair A ell k) u omega =
        gCorr (L := L) (m := m) (rm := rm) A u ell omega +
          gCorr (L := L) (m := m) (rm := rm) A u k omega := by
    unfold M_u_corr_layerAvg
    have hConst :
        (∑ ell' : Fin L, gCorr (L := L) (m := m) (rm := rm) (ArowPair A ell k) u ell' omega) =
          ∑ ell' : Fin L,
            (gCorr (L := L) (m := m) (rm := rm) A u ell omega +
              gCorr (L := L) (m := m) (rm := rm) A u k omega) := by
      refine Finset.sum_congr rfl ?_
      intro ell' hEll'
      exact gCorr_ArowPair_eq A u ell k ell' omega
    rw [hConst, Finset.sum_const, nsmul_eq_mul]
    simp
    field_simp [hL0]
  have hBridge := congrArg (fun f => f omega)
    (M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) (A := ArowPair A ell k) u)
  calc
    gCorr (L := L) (m := m) (rm := rm) A u ell omega +
        gCorr (L := L) (m := m) (rm := rm) A u k omega
        = M_u_corr_layerAvg (L := L) (m := m) (rm := rm) (ArowPair A ell k) u omega := by
            exact hAvg.symm
    _ = M_u_corr (L := L) (m := m) (rm := rm) (ArowPair A ell k) u omega := hBridge

theorem map_gCorr_gaussian_any
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell : Fin L) :
    (muCorr L m rm).map
      (fun omega => gCorr (L := L) (m := m) (rm := rm) A u ell omega) =
      gaussianReal 0 (vecVarCorr L (Arow A ell) u) := by
  have hEq := gCorr_eq_M_u_corr_Arow (L := L) (m := m) (rm := rm) hL A u ell
  simpa [hEq] using
    map_M_u_corr_gaussian_any (L := L) (m := m) (rm := rm) hL hrm (Arow A ell) u

theorem map_gCorr_add_gaussian_any
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell k : Fin L) :
    (muCorr L m rm).map
      (fun omega =>
        gCorr (L := L) (m := m) (rm := rm) A u ell omega +
          gCorr (L := L) (m := m) (rm := rm) A u k omega) =
      gaussianReal 0 (vecVarCorr L (ArowPair A ell k) u) := by
  have hEq := gCorr_add_eq_M_u_corr_ArowPair (L := L) (m := m) (rm := rm) hL A u ell k
  simpa [hEq] using
    map_M_u_corr_gaussian_any (L := L) (m := m) (rm := rm) hL hrm (ArowPair A ell k) u

lemma memLp_two_of_map_gaussian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω -> Real) (v : NNReal)
    (hMap : μ.map X = gaussianReal 0 v) :
    MemLp X (2 : ENNReal) μ := by
  have hMemId : MemLp id (2 : ENNReal) (gaussianReal (0 : Real) v) := by
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : Real)) (v := v) (p := (2 : NNReal)))
  have hMemMap : MemLp id (2 : ENNReal) (μ.map X) := by
    simpa [hMap] using hMemId
  have hAemeas : AEMeasurable X μ := aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  exact
    (MeasureTheory.memLp_map_measure_iff
      (p := (2 : ENNReal))
      (μ := μ)
      (f := X)
      (g := id)
      (hg := measurable_id.aestronglyMeasurable)
      (hf := hAemeas)).mp hMemMap

lemma memLp_two_gCorr
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell : Fin L) :
    MemLp
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega)
      (2 : ENNReal) (muCorr L m rm) := by
  have hMap := map_gCorr_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A u ell
  exact memLp_two_of_map_gaussian (μ := muCorr L m rm)
    (X := fun omega => gCorr (L := L) (m := m) (rm := rm) A u ell omega)
    (v := vecVarCorr L (Arow A ell) u) hMap

lemma memLp_two_gCorr_add
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell k : Fin L) :
    MemLp
      (fun omega : OmegaCorr L m rm =>
        gCorr (L := L) (m := m) (rm := rm) A u ell omega +
          gCorr (L := L) (m := m) (rm := rm) A u k omega)
      (2 : ENNReal) (muCorr L m rm) := by
  have hMap := map_gCorr_add_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A u ell k
  exact memLp_two_of_map_gaussian (μ := muCorr L m rm)
    (X := fun omega =>
      gCorr (L := L) (m := m) (rm := rm) A u ell omega +
        gCorr (L := L) (m := m) (rm := rm) A u k omega)
    (v := vecVarCorr L (ArowPair A ell k) u) hMap

theorem variance_gCorr
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell : Fin L) :
    variance
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega)
      (muCorr L m rm) =
      norm u ^ 2 * rho A ell ell / (L : Real) := by
  have hMap := map_gCorr_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A u ell
  have hAemeas :
      AEMeasurable
        (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega)
        (muCorr L m rm) := by
    exact aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  calc
    variance
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega)
      (muCorr L m rm)
        = variance id ((muCorr L m rm).map
            (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega)) := by
              simpa using
                (variance_id_map
                  (μ := muCorr L m rm)
                  (X := fun omega : OmegaCorr L m rm =>
                    gCorr (L := L) (m := m) (rm := rm) A u ell omega)
                  hAemeas).symm
    _ = variance id (gaussianReal 0 (vecVarCorr L (Arow A ell) u)) := by rw [hMap]
    _ = (vecVarCorr L (Arow A ell) u : Real) := by simp
    _ = norm u ^ 2 * rho A ell ell / (L : Real) := by
          calc
            (vecVarCorr L (Arow A ell) u : Real)
                = norm u ^ 2 * rhoSum (Arow A ell) / (L : Real) ^ 3 := by
                    simp [vecVarCorr]
            _ = norm u ^ 2 * ((L : Real) ^ 2 * rho A ell ell) / (L : Real) ^ 3 := by
                  rw [rhoSum_Arow]
            _ = norm u ^ 2 * rho A ell ell / (L : Real) := by
                  field_simp [hL0]

theorem variance_gCorr_add
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell k : Fin L) :
    variance
      (fun omega : OmegaCorr L m rm =>
        gCorr (L := L) (m := m) (rm := rm) A u ell omega +
          gCorr (L := L) (m := m) (rm := rm) A u k omega)
      (muCorr L m rm) =
      norm u ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k) / (L : Real) := by
  have hMap := map_gCorr_add_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A u ell k
  have hAemeas :
      AEMeasurable
        (fun omega : OmegaCorr L m rm =>
          gCorr (L := L) (m := m) (rm := rm) A u ell omega +
            gCorr (L := L) (m := m) (rm := rm) A u k omega)
        (muCorr L m rm) := by
    exact aemeasurable_of_map_neZero (by rw [hMap]; infer_instance)
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  calc
    variance
      (fun omega : OmegaCorr L m rm =>
        gCorr (L := L) (m := m) (rm := rm) A u ell omega +
          gCorr (L := L) (m := m) (rm := rm) A u k omega)
      (muCorr L m rm)
        = variance id ((muCorr L m rm).map
            (fun omega : OmegaCorr L m rm =>
              gCorr (L := L) (m := m) (rm := rm) A u ell omega +
                gCorr (L := L) (m := m) (rm := rm) A u k omega)) := by
                  simpa using
                    (variance_id_map
                      (μ := muCorr L m rm)
                      (X := fun omega : OmegaCorr L m rm =>
                        gCorr (L := L) (m := m) (rm := rm) A u ell omega +
                          gCorr (L := L) (m := m) (rm := rm) A u k omega)
                      hAemeas).symm
    _ = variance id (gaussianReal 0 (vecVarCorr L (ArowPair A ell k) u)) := by rw [hMap]
    _ = (vecVarCorr L (ArowPair A ell k) u : Real) := by simp
    _ = norm u ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k) / (L : Real) := by
          calc
            (vecVarCorr L (ArowPair A ell k) u : Real)
                = norm u ^ 2 * rhoSum (ArowPair A ell k) / (L : Real) ^ 3 := by
                    simp [vecVarCorr]
            _ = norm u ^ 2 *
                ((L : Real) ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k)) / (L : Real) ^ 3 := by
                  rw [rhoSum_ArowPair]
            _ = norm u ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k) / (L : Real) := by
                  field_simp [hL0]

theorem cov_gCorr
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (ell k : Fin L) :
    cov[
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega),
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u k omega);
      muCorr L m rm] =
      (rho A ell k / (L : Real)) * (norm u ^ 2) := by
  haveI : IsProbabilityMeasure (muCorr L m rm) := by
    unfold muCorr muLatent muSharedZ gaussianPi
    infer_instance
  let Xell : OmegaCorr L m rm -> Real :=
    fun omega => gCorr (L := L) (m := m) (rm := rm) A u ell omega
  let Xk : OmegaCorr L m rm -> Real :=
    fun omega => gCorr (L := L) (m := m) (rm := rm) A u k omega
  have hMemEll : MemLp Xell (2 : ENNReal) (muCorr L m rm) := by
    simpa [Xell] using memLp_two_gCorr (L := L) (m := m) (rm := rm) hL hrm A u ell
  have hMemK : MemLp Xk (2 : ENNReal) (muCorr L m rm) := by
    simpa [Xk] using memLp_two_gCorr (L := L) (m := m) (rm := rm) hL hrm A u k
  have hVarAdd :
      Var[Xell + Xk; muCorr L m rm] =
        Var[Xell; muCorr L m rm] + 2 * cov[Xell, Xk; muCorr L m rm] + Var[Xk; muCorr L m rm] :=
    variance_add hMemEll hMemK
  have hVarEll :
      Var[Xell; muCorr L m rm] = norm u ^ 2 * rho A ell ell / (L : Real) := by
    simpa [Xell] using variance_gCorr (L := L) (m := m) (rm := rm) hL hrm A u ell
  have hVarK :
      Var[Xk; muCorr L m rm] = norm u ^ 2 * rho A k k / (L : Real) := by
    simpa [Xk] using variance_gCorr (L := L) (m := m) (rm := rm) hL hrm A u k
  have hVarSum :
      Var[Xell + Xk; muCorr L m rm] =
        norm u ^ 2 * (rho A ell ell + rho A k k + 2 * rho A ell k) / (L : Real) := by
    simpa [Xell, Xk] using variance_gCorr_add (L := L) (m := m) (rm := rm) hL hrm A u ell k
  have hCov :
      cov[Xell, Xk; muCorr L m rm] =
        (Var[Xell + Xk; muCorr L m rm] - Var[Xell; muCorr L m rm] - Var[Xk; muCorr L m rm]) / 2 := by
    linarith [hVarAdd]
  calc
    cov[
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u ell omega),
      (fun omega : OmegaCorr L m rm => gCorr (L := L) (m := m) (rm := rm) A u k omega);
      muCorr L m rm]
        = cov[Xell, Xk; muCorr L m rm] := by rfl
    _ = (Var[Xell + Xk; muCorr L m rm] - Var[Xell; muCorr L m rm] - Var[Xk; muCorr L m rm]) / 2 := hCov
    _ = (rho A ell k / (L : Real)) * (norm u ^ 2) := by
          rw [hVarSum, hVarEll, hVarK]
          ring

end

end Correlated
end NNGPResNet
end LeanSlt
