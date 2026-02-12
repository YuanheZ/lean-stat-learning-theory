import LeanSlt.NNGPResNet.Correlated.GaussianLinearForms
import LeanSlt.EffectiveDepthConcentration

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet
namespace Correlated

noncomputable section

def invDEffNNReal {L : Nat} (A : Fin L -> Fin L -> Real) : NNReal :=
  Subtype.mk (rhoSum A / (L : Real) ^ 3) (by
    have hNum : 0 <= rhoSum A := rhoSum_nonneg A
    have hDen : 0 <= (L : Real) ^ 3 := by positivity
    exact div_nonneg hNum hDen)

theorem corr_scalar_map_gaussian_any
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    (muCorr L m rm).map (M_u_corr (L := L) (m := m) (rm := rm) A u)
      = gaussianReal 0 (vecVarCorr L A u) :=
  map_M_u_corr_gaussian_any hL hrm A u

theorem corr_scalar_map_gaussian_any_layerAvg
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    (muCorr L m rm).map (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u)
      = gaussianReal 0 (vecVarCorr L A u) := by
  simpa [M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A u] using
    corr_scalar_map_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A u

theorem corr_scalar_map_gaussian_unit
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    (muCorr L m rm).map (M_u_corr (L := L) (m := m) (rm := rm) A u)
      = gaussianReal 0 (invDEffNNReal A) := by
  have hMap := corr_scalar_map_gaussian_any (L := L) (m := m) (rm := rm) hL hrm A u
  have hNormSq : norm u ^ 2 = 1 := by nlinarith [hu]
  have hVar : (vecVarCorr L A u : Real) = rhoSum A / (L : Real) ^ 3 := by
    simp [vecVarCorr, hNormSq]
  have hVarEq : vecVarCorr L A u = invDEffNNReal A := by
    apply Subtype.ext
    simpa [invDEffNNReal] using hVar
  simpa [hVarEq] using hMap

theorem corr_scalar_map_gaussian_unit_layerAvg
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    (muCorr L m rm).map (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u)
      = gaussianReal 0 (invDEffNNReal A) := by
  simpa [M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A u] using
    corr_scalar_map_gaussian_unit (L := L) (m := m) (rm := rm) hL hrm A u hu

theorem corr_scalar_tail
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1)
    (hRhoPos : 0 < rhoSum A) :
    forall t : Real, 0 < t ->
      ((muCorr L m rm) {omega | abs (M_u_corr (L := L) (m := m) (rm := rm) A u omega) >= t}).toReal <=
        2 * Real.exp (-(t ^ 2) * (D_eff A) / 2) := by
  have hMap := corr_scalar_map_gaussian_unit (L := L) (m := m) (rm := rm) hL hrm A u hu
  haveI : IsProbabilityMeasure (muCorr L m rm) := by
    unfold muCorr muLatent muSharedZ gaussianPi
    infer_instance
  have hvPos : 0 < ((invDEffNNReal A : NNReal) : Real) := by
    change 0 < rhoSum A / (L : Real) ^ 3
    have hLpos : 0 < (L : Real) ^ 3 := by positivity
    exact div_pos hRhoPos hLpos
  have hBase :=
    abs_tail_le_two_exp_of_map_gaussian
      (mu := muCorr L m rm)
      (M := M_u_corr (L := L) (m := m) (rm := rm) A u)
      (v := invDEffNNReal A) hvPos hMap
  intro t ht
  have hRho0 : rhoSum A ≠ 0 := ne_of_gt hRhoPos
  have hExp :
      (-t ^ 2 / (2 * ((invDEffNNReal A : NNReal) : Real))) = (-(t ^ 2) * (D_eff A) / 2) := by
    have hInv : ((invDEffNNReal A : NNReal) : Real) = rhoSum A / (L : Real) ^ 3 := by
      simp [invDEffNNReal]
    rw [hInv]
    unfold D_eff
    field_simp [hRho0]
  calc
    ((muCorr L m rm) {omega | abs (M_u_corr (L := L) (m := m) (rm := rm) A u omega) >= t}).toReal
      <= 2 * Real.exp (-t ^ 2 / (2 * ((invDEffNNReal A : NNReal) : Real))) := hBase t ht
    _ = 2 * Real.exp (-(t ^ 2) * (D_eff A) / 2) := by rw [hExp]

theorem corr_scalar_tail_layerAvg
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1)
    (hRhoPos : 0 < rhoSum A) :
    forall t : Real, 0 < t ->
      ((muCorr L m rm) {omega | abs (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u omega) >= t}).toReal <=
        2 * Real.exp (-(t ^ 2) * (D_eff A) / 2) := by
  intro t ht
  simpa [M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A u] using
    corr_scalar_tail (L := L) (m := m) (rm := rm) hL hrm A u hu hRhoPos t ht

theorem corr_scalar_mse
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    (integral (muCorr L m rm)
      (fun omega => (M_u_corr (L := L) (m := m) (rm := rm) A u omega) ^ 2))
        = rhoSum A / (L : Real) ^ 3 := by
  have hMap := corr_scalar_map_gaussian_unit (L := L) (m := m) (rm := rm) hL hrm A u hu
  haveI : IsProbabilityMeasure (muCorr L m rm) := by
    unfold muCorr muLatent muSharedZ gaussianPi
    infer_instance
  have hMse :=
    mse_of_map_gaussian
      (mu := muCorr L m rm)
      (M := M_u_corr (L := L) (m := m) (rm := rm) A u)
      (v := invDEffNNReal A) hMap
  simpa [invDEffNNReal] using hMse

theorem corr_scalar_mse_layerAvg
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    (integral (muCorr L m rm)
      (fun omega => (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u omega) ^ 2))
        = rhoSum A / (L : Real) ^ 3 := by
  simpa [M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A u] using
    corr_scalar_mse (L := L) (m := m) (rm := rm) hL hrm A u hu

theorem var_M_u_corr_layerAvg
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    variance (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm)
      = norm u ^ 2 * rhoSum A / (L : Real) ^ 3 := by
  have hMap := corr_scalar_map_gaussian_any_layerAvg (L := L) (m := m) (rm := rm) hL hrm A u
  have hMeas :
      AEMeasurable (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm) := by
    have hM : Measurable (M_u_corr (L := L) (m := m) (rm := rm) A u) :=
      measurable_M_u_corr (L := L) (m := m) (rm := rm) A u
    refine hM.aemeasurable.congr ?_
    exact Filter.Eventually.of_forall (fun omega =>
      (congrArg (fun f => f omega)
        (M_u_corr_layerAvg_eq_M_u_corr (L := L) (m := m) (rm := rm) A u)).symm)
  calc
    variance (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm)
        = variance id ((muCorr L m rm).map (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u)) := by
            simpa using
              (variance_id_map
                (μ := muCorr L m rm)
                (X := M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u)
                hMeas).symm
    _ = variance id (gaussianReal 0 (vecVarCorr L A u)) := by rw [hMap]
    _ = (vecVarCorr L A u : Real) := by simp
    _ = norm u ^ 2 * rhoSum A / (L : Real) ^ 3 := by simp [vecVarCorr]

theorem var_M_u_corr_layerAvg_as_covariance_sum
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    variance (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm)
      = (1 / (L : Real) ^ 2) *
          (∑ ell : Fin L, ∑ k : Fin L,
            cov[
              (fun omega : OmegaCorr L m rm =>
                gCorr (L := L) (m := m) (rm := rm) A u ell omega),
              (fun omega : OmegaCorr L m rm =>
                gCorr (L := L) (m := m) (rm := rm) A u k omega);
              muCorr L m rm]) := by
  haveI : IsProbabilityMeasure (muCorr L m rm) := by
    unfold muCorr muLatent muSharedZ gaussianPi
    infer_instance
  let gFn : Fin L -> OmegaCorr L m rm -> Real :=
    fun ell omega => gCorr (L := L) (m := m) (rm := rm) A u ell omega
  have hMem : ∀ ell : Fin L, MemLp (gFn ell) (2 : ENNReal) (muCorr L m rm) := by
    intro ell
    simpa [gFn] using memLp_two_gCorr (L := L) (m := m) (rm := rm) hL hrm A u ell
  have hVarSum :
      Var[fun omega => ∑ ell : Fin L, gFn ell omega; muCorr L m rm] =
        ∑ ell : Fin L, ∑ k : Fin L, cov[gFn ell, gFn k; muCorr L m rm] := by
    simpa [gFn] using
      (variance_fun_sum (μ := muCorr L m rm) (X := gFn) hMem)
  calc
    variance (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm)
      = variance (fun omega => (1 / (L : Real)) * ∑ ell : Fin L, gFn ell omega) (muCorr L m rm) := by
          rfl
    _ = (1 / (L : Real)) ^ 2 *
          variance (fun omega => ∑ ell : Fin L, gFn ell omega) (muCorr L m rm) := by
          simpa using
            (variance_const_mul (1 / (L : Real))
              (fun omega => ∑ ell : Fin L, gFn ell omega) (muCorr L m rm))
    _ = (1 / (L : Real) ^ 2) *
          (∑ ell : Fin L, ∑ k : Fin L, cov[gFn ell, gFn k; muCorr L m rm]) := by
          rw [hVarSum]
          ring

theorem var_M_u_corr_layerAvg_as_rho_sum
    {L m rm : Nat}
    (hL : 0 < L) (hrm : 0 < rm)
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    variance (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm)
      = (1 / (L : Real) ^ 2) *
          (∑ ell : Fin L, ∑ k : Fin L, ((rho A ell k) / (L : Real)) * (norm u ^ 2)) := by
  have hCovSum := var_M_u_corr_layerAvg_as_covariance_sum
    (L := L) (m := m) (rm := rm) hL hrm A u
  calc
    variance (M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u) (muCorr L m rm)
      = (1 / (L : Real) ^ 2) *
          (∑ ell : Fin L, ∑ k : Fin L,
            cov[
              (fun omega : OmegaCorr L m rm =>
                gCorr (L := L) (m := m) (rm := rm) A u ell omega),
              (fun omega : OmegaCorr L m rm =>
                gCorr (L := L) (m := m) (rm := rm) A u k omega);
              muCorr L m rm]) := hCovSum
    _ = (1 / (L : Real) ^ 2) *
          (∑ ell : Fin L, ∑ k : Fin L, ((rho A ell k) / (L : Real)) * (norm u ^ 2)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro ell hEll
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa using cov_gCorr (L := L) (m := m) (rm := rm) hL hrm A u ell k

def A_indep (L : Nat) : Fin L -> Fin L -> Real :=
  fun ell t => if ell = t then 1 else 0

def A_full (L : Nat) (hL : 0 < L) : Fin L -> Fin L -> Real :=
  fun _ t => if t = Fin.mk 0 hL then 1 else 0

lemma rhoSum_A_indep (L : Nat) :
    rhoSum (A_indep L) = (L : Real) := by
  rw [rhoSum_eq_sum_sq_colSums]
  simp [sumACol, A_indep]

lemma rhoSum_A_full (L : Nat) (hL : 0 < L) :
    rhoSum (A_full L hL) = (L : Real) ^ 2 := by
  rw [rhoSum_eq_sum_sq_colSums]
  let t0 : Fin L := Fin.mk 0 hL
  have hcol : ∀ t : Fin L, sumACol (A_full L hL) t = if t = t0 then (L : Real) else 0 := by
    intro t
    unfold sumACol A_full
    by_cases ht : t = t0
    · subst ht
      simp [t0]
    · simp [t0, ht]
  calc
    Finset.univ.sum (fun t : Fin L => (sumACol (A_full L hL) t) ^ 2)
        = Finset.univ.sum (fun t : Fin L => (if t = t0 then (L : Real) else 0) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp [hcol t]
    _ = (L : Real) ^ 2 := by
          simp [t0]

lemma D_eff_A_indep (L : Nat) (hL : 0 < L) :
    D_eff (A_indep L) = (L : Real) ^ 2 := by
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  calc
    D_eff (A_indep L) = (L : Real) ^ 3 / rhoSum (A_indep L) := by rfl
    _ = (L : Real) ^ 3 / (L : Real) := by rw [rhoSum_A_indep]
    _ = (L : Real) ^ 2 := by
          field_simp [hL0]

lemma D_eff_A_full (L : Nat) (hL : 0 < L) :
    D_eff (A_full L hL) = (L : Real) := by
  have hL0 : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  calc
    D_eff (A_full L hL) = (L : Real) ^ 3 / rhoSum (A_full L hL) := by rfl
    _ = (L : Real) ^ 3 / (L : Real) ^ 2 := by rw [rhoSum_A_full L hL]
    _ = (L : Real) := by
          field_simp [hL0]

end

end Correlated
end NNGPResNet
end LeanSlt
