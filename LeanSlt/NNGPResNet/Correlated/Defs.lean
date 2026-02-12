import LeanSlt.NNGPResNet.Defs

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet
namespace Correlated

noncomputable section

abbrev LatentIdx (L m rm : Nat) := Prod (Fin L) (Prod (Fin m) (Fin rm))
abbrev LatentSpace (L m rm : Nat) := LatentIdx L m rm -> Real
abbrev SharedZSpace (rm : Nat) := Fin rm -> Real
abbrev OmegaCorr (L m rm : Nat) := Prod (LatentSpace L m rm) (SharedZSpace rm)

noncomputable def muLatent (L m rm : Nat) : Measure (LatentSpace L m rm) :=
  gaussianPi (LatentIdx L m rm)

noncomputable def muSharedZ (rm : Nat) : Measure (SharedZSpace rm) :=
  gaussianPi (Fin rm)

noncomputable def muCorr (L m rm : Nat) : Measure (OmegaCorr L m rm) :=
  (muLatent L m rm).prod (muSharedZ rm)

def latentCoord {L m rm : Nat} (omega : OmegaCorr L m rm)
    (t : Fin L) (i : Fin m) (j : Fin rm) : Real :=
  omega.1 (t, (i, j))

def zCoord {L m rm : Nat} (omega : OmegaCorr L m rm) (j : Fin rm) : Real :=
  omega.2 j

def aCoord {L m rm : Nat} (omega : OmegaCorr L m rm) (j : Fin rm) : Real :=
  signAct (zCoord omega j)

def rho {L : Nat} (A : Fin L -> Fin L -> Real) (ell k : Fin L) : Real :=
  Finset.univ.sum (fun t : Fin L => A ell t * A k t)

def sumACol {L : Nat} (A : Fin L -> Fin L -> Real) (t : Fin L) : Real :=
  Finset.univ.sum (fun ell : Fin L => A ell t)

def rhoSum {L : Nat} (A : Fin L -> Fin L -> Real) : Real :=
  Finset.univ.sum (fun ell : Fin L => Finset.univ.sum (fun k : Fin L => rho A ell k))

def invDEff {L : Nat} (A : Fin L -> Fin L -> Real) : Real :=
  rhoSum A / (L : Real) ^ 3

def D_eff {L : Nat} (A : Fin L -> Fin L -> Real) : Real :=
  (L : Real) ^ 3 / rhoSum A

lemma rhoSum_eq_sum_sq_colSums {L : Nat} (A : Fin L -> Fin L -> Real) :
    rhoSum A = Finset.univ.sum (fun t : Fin L => (sumACol A t) ^ 2) := by
  unfold rhoSum rho sumACol
  calc
    (∑ ell : Fin L, ∑ k : Fin L, ∑ t : Fin L, A ell t * A k t)
        = ∑ k : Fin L, ∑ ell : Fin L, ∑ t : Fin L, A ell t * A k t := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin L, ∑ t : Fin L, ∑ ell : Fin L, A ell t * A k t := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Finset.sum_comm]
    _ = ∑ t : Fin L, ∑ k : Fin L, ∑ ell : Fin L, A ell t * A k t := by
          rw [Finset.sum_comm]
    _ = ∑ t : Fin L, ∑ ell : Fin L, ∑ k : Fin L, A ell t * A k t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [Finset.sum_comm]
    _ = ∑ t : Fin L, (∑ ell : Fin L, A ell t) * (∑ k : Fin L, A k t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          symm
          rw [Finset.sum_mul_sum]
    _ = ∑ t : Fin L, (∑ ell : Fin L, A ell t) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring

lemma rhoSum_nonneg {L : Nat} (A : Fin L -> Fin L -> Real) :
    0 <= rhoSum A := by
  rw [rhoSum_eq_sum_sq_colSums]
  exact Finset.sum_nonneg (fun t ht => sq_nonneg _)

def corrScale (L rm : Nat) : Real :=
  (1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real))

def Bcorr {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    (omega : OmegaCorr L m rm) (ell : Fin L) (i : Fin m) (j : Fin rm) : Real :=
  Finset.univ.sum (fun t : Fin L => A ell t * latentCoord omega t i j)

def deltaHCorr {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    (ell : Fin L) (omega : OmegaCorr L m rm) : Fin m -> Real :=
  fun i =>
    (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
      Finset.univ.sum (fun j : Fin rm => Bcorr A omega ell i j * aCoord omega j)

def gCorr {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) (ell : Fin L) (omega : OmegaCorr L m rm) : Real :=
  Finset.univ.sum (fun i : Fin m => u i * deltaHCorr A ell omega i)

def M_u_corr_layerAvg {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) : OmegaCorr L m rm -> Real :=
  fun omega =>
    (1 / (L : Real)) * Finset.univ.sum (fun ell : Fin L => gCorr (L := L) (m := m) (rm := rm) A u ell omega)

def M_u_corr {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) : OmegaCorr L m rm -> Real :=
  fun omega =>
    Finset.univ.sum (fun idx : LatentIdx L m rm =>
      corrScale L rm * u idx.2.1 * sumACol A idx.1 *
        aCoord omega idx.2.2 * latentCoord omega idx.1 idx.2.1 idx.2.2)

lemma M_u_corr_layerAvg_eq_M_u_corr
    {L m rm : Nat}
    (A : Fin L -> Fin L -> Real)
    (u : EuclideanSpace Real (Fin m)) :
    M_u_corr_layerAvg (L := L) (m := m) (rm := rm) A u =
      M_u_corr (L := L) (m := m) (rm := rm) A u := by
  funext omega
  let T : Fin L → Fin m → Fin rm → Fin L → Real := fun ell i j t =>
    A ell t *
      ((1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
        (aCoord omega j * (latentCoord omega t i j * u i)))
  have hswap :
      (∑ ell : Fin L, ∑ i : Fin m, ∑ j : Fin rm, ∑ t : Fin L, T ell i j t) =
        (∑ t : Fin L, ∑ i : Fin m, ∑ j : Fin rm, ∑ ell : Fin L, T ell i j t) := by
    let Q := Prod (Fin L) (Prod (Fin m) (Prod (Fin rm) (Fin L)))
    let e : Q -> Q := fun q =>
      match q with
      | (ell, (i, (j, t))) => (t, (i, (j, ell)))
    have hInv : Function.LeftInverse e e := by
      intro q
      cases q
      rfl
    have he : Function.Bijective e := ⟨hInv.injective, hInv.surjective⟩
    have hsum := Fintype.sum_bijective
      e he
      (fun q : Q => T q.1 q.2.1 q.2.2.1 q.2.2.2)
      (fun q : Q => T q.2.2.2 q.2.1 q.2.2.1 q.1)
      (by
        intro q
        cases q with
        | mk a q =>
            cases q with
            | mk b q =>
                cases q with
                | mk c d =>
                    rfl
      )
    have hsum' : (∑ q : Q, T q.1 q.2.1 q.2.2.1 q.2.2.2)
        = ∑ q : Q, T q.2.2.2 q.2.1 q.2.2.1 q.1 := by
      simpa using hsum
    simpa [Q, Fintype.sum_prod_type] using hsum'
  unfold M_u_corr_layerAvg gCorr deltaHCorr Bcorr M_u_corr corrScale sumACol
  have hExpanded :
      (1 / (L : Real)) *
          ∑ ell : Fin L,
            ∑ i : Fin m,
              u i * ((1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
                ∑ j : Fin rm, (∑ t : Fin L, A ell t * latentCoord omega t i j) * aCoord omega j)
        =
      ∑ ell : Fin L, ∑ i : Fin m, ∑ j : Fin rm, ∑ t : Fin L, T ell i j t := by
    unfold T
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  calc
    (1 / (L : Real)) *
        ∑ ell : Fin L,
          ∑ i : Fin m,
            u i * ((1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
              ∑ j : Fin rm, (∑ t : Fin L, A ell t * latentCoord omega t i j) * aCoord omega j)
        = ∑ ell : Fin L, ∑ i : Fin m, ∑ j : Fin rm, ∑ t : Fin L, T ell i j t := hExpanded
    _ = ∑ t : Fin L, ∑ i : Fin m, ∑ j : Fin rm, ∑ ell : Fin L, T ell i j t := hswap
    _ = ∑ t : Fin L, ∑ i : Fin m, ∑ j : Fin rm,
          ((1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real))) *
            u i * (∑ ell : Fin L, A ell t) * aCoord omega j * latentCoord omega t i j := by
          unfold T
          refine Finset.sum_congr rfl ?_
          intro t ht
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          have :
              (∑ ell : Fin L,
                  A ell t *
                    ((1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
                      (aCoord omega j * (latentCoord omega t i j * u i))))
                =
              (∑ ell : Fin L, A ell t) *
                ((1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
                  (aCoord omega j * (latentCoord omega t i j * u i))) := by
                rw [Finset.sum_mul]
          rw [this]
          ring
    _ = ∑ idx : LatentIdx L m rm,
          ((1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real))) *
            u idx.2.1 * (∑ ell : Fin L, A ell idx.1) * aCoord omega idx.2.2 *
              latentCoord omega idx.1 idx.2.1 idx.2.2 := by
          simp [Fintype.sum_prod_type]

def Wcorr {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    : OmegaCorr L m rm -> (Fin m -> Real) :=
  fun omega i =>
    Finset.univ.sum (fun idx : Prod (Fin L) (Fin rm) =>
      corrScale L rm * sumACol A idx.1 * aCoord omega idx.2 *
        latentCoord omega idx.1 i idx.2)

def XCorr {L m rm : Nat} (A : Fin L -> Fin L -> Real)
    : Sphere m -> OmegaCorr L m rm -> Real :=
  fun u omega => Finset.univ.sum (fun i : Fin m => u.1 i * Wcorr A omega i)

end

end Correlated
end NNGPResNet
end LeanSlt
