import LeanSlt.NNGPResNet.GaussianLinearForms
import LeanSlt.EffectiveDepthConcentration

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet

noncomputable section

def invLSqNNReal (L : Nat) : NNReal :=
  Subtype.mk (1 / (L : Real) ^ 2) (by positivity)

theorem scalar_mean_map_gaussian
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    (muNN L m rm).map (M_u (L := L) (m := m) (rm := rm) u)
      = gaussianReal 0 (invLSqNNReal L) := by
  have hMapAny := map_M_u_gaussian_any (m := m) (L := L) (rm := rm) hL hrm u
  have hNormSq : norm u ^ 2 = 1 := by
    nlinarith [hu]
  have hVar : (vecVarNN L u : Real) = 1 / (L : Real) ^ 2 := by
    simp [vecVarNN, hNormSq]
  have hVarEq : vecVarNN L u = invLSqNNReal L := by
    apply Subtype.ext
    simpa [invLSqNNReal] using hVar
  simpa [hVarEq] using hMapAny

theorem scalar_mean_tail
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    forall t : Real, 0 < t ->
      ((muNN L m rm) {omega | abs (M_u (L := L) (m := m) (rm := rm) u omega) >= t}).toReal <=
        2 * Real.exp (-(L : Real) ^ 2 * t ^ 2 / 2) := by
  have hMap := scalar_mean_map_gaussian (m := m) (L := L) (rm := rm) hL hrm u hu
  haveI : IsProbabilityMeasure (muNN L m rm) := by
    unfold muNN muG muZ gaussianPi
    infer_instance
  have hvPos : 0 < ((invLSqNNReal L : NNReal) : Real) := by
    have hLReal : 0 < (L : Real) := by exact_mod_cast hL
    simp [invLSqNNReal, hLReal]
  have hBase :=
    abs_tail_le_two_exp_of_map_gaussian
      (mu := muNN L m rm)
      (M := M_u (L := L) (m := m) (rm := rm) u)
      (v := invLSqNNReal L) hvPos hMap
  intro t ht
  have hL0 : Ne (L : Real) 0 := by
    exact_mod_cast (Nat.ne_of_gt hL)
  have hExp :
      (-t ^ 2 / (2 * ((invLSqNNReal L : NNReal) : Real)))
        = (-(L : Real) ^ 2 * t ^ 2 / 2) := by
    have hInv : ((invLSqNNReal L : NNReal) : Real) = 1 / (L : Real) ^ 2 := by
      simp [invLSqNNReal]
    rw [hInv]
    field_simp [hL0]
  calc
    ((muNN L m rm) {omega | abs (M_u (L := L) (m := m) (rm := rm) u omega) >= t}).toReal
      <= 2 * Real.exp (-t ^ 2 / (2 * ((invLSqNNReal L : NNReal) : Real))) :=
        hBase t ht
    _ = 2 * Real.exp (-(L : Real) ^ 2 * t ^ 2 / 2) := by rw [hExp]

theorem scalar_mean_mse
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (u : EuclideanSpace Real (Fin m))
    (hu : norm u = 1) :
    (integral (muNN L m rm)
      (fun omega => (M_u (L := L) (m := m) (rm := rm) u omega) ^ 2))
        = 1 / (L : Real) ^ 2 := by
  have hMap := scalar_mean_map_gaussian (m := m) (L := L) (rm := rm) hL hrm u hu
  haveI : IsProbabilityMeasure (muNN L m rm) := by
    unfold muNN muG muZ gaussianPi
    infer_instance
  have hMse :=
    mse_of_map_gaussian
      (mu := muNN L m rm)
      (M := M_u (L := L) (m := m) (rm := rm) u)
      (v := invLSqNNReal L) hMap
  simpa [invLSqNNReal] using hMse

end

end NNGPResNet
end LeanSlt
