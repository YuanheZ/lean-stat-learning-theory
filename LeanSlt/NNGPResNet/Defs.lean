import Mathlib
import SLT.GaussianMeasure
import SLT.LeastSquares.LinearRegression.DesignMatrix

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet

noncomputable section

/-- Residual width proxy `rm = r * m`. -/
def residualWidth (m r : Nat) : Nat := r * m

/-- Identity design used to instantiate linear-entropy bounds from SLT. -/
def xId (m : Nat) : Fin m -> EuclideanSpace Real (Fin m) :=
  fun i => EuclideanSpace.single i (1 : Real)

/-- Sign activation used in the residual toy model (`+-1` valued). -/
def signAct (x : Real) : Real := if 0 <= x then 1 else -1

/-- Layerwise activation vector `a_l(j) = sign(z_l(j))`. -/
def activationVec {L rm : Nat}
    (z : Fin L -> Fin rm -> Real) (ell : Fin L) : Fin rm -> Real :=
  fun j => signAct (z ell j)

/--
Residual increment for layer `ell`:
`delta_h_ell = (1/sqrt L) * (1/sqrt rm) * B_ell * a_ell`.
-/
def deltaH {L m rm : Nat}
    (B : Fin L -> Fin m -> Fin rm -> Real)
    (z : Fin L -> Fin rm -> Real) (ell : Fin L) : Fin m -> Real :=
  fun i =>
    (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real)) *
      Finset.univ.sum (fun j : Fin rm => B ell i j * activationVec z ell j)

/-- Scalar probe `g_ell = <u, delta_h_ell>`. -/
def gLayer {L m rm : Nat}
    (B : Fin L -> Fin m -> Fin rm -> Real)
    (z : Fin L -> Fin rm -> Real)
    (u : EuclideanSpace Real (Fin m)) (ell : Fin L) : Real :=
  Finset.univ.sum (fun i : Fin m => u i * deltaH B z ell i)

/-- Depth-average scalar probe from layerwise probes. -/
def meanProbe {L m rm : Nat}
    (B : Fin L -> Fin m -> Fin rm -> Real)
    (z : Fin L -> Fin rm -> Real)
    (u : EuclideanSpace Real (Fin m)) : Real :=
  (1 / (L : Real)) * Finset.univ.sum (fun ell : Fin L => gLayer B z u ell)

/-- Product Gaussian measure on a finite coordinate type. -/
noncomputable def gaussianPi (idxType : Type*) [Fintype idxType] [DecidableEq idxType] :
    Measure (idxType -> Real) :=
  Measure.pi (fun _ : idxType => gaussianReal 0 1)

/-- Flattened index for Gaussian weights `B_(ell,i,j)`. -/
abbrev GIdx (L m rm : Nat) := Prod (Fin L) (Prod (Fin m) (Fin rm))

/-- Flattened index for pre-activations `z_(ell,j)`. -/
abbrev ZIdx (L rm : Nat) := Prod (Fin L) (Fin rm)

abbrev GSpace (L m rm : Nat) := GIdx L m rm -> Real
abbrev ZSpace (L rm : Nat) := ZIdx L rm -> Real
abbrev OmegaNN (L m rm : Nat) := Prod (GSpace L m rm) (ZSpace L rm)

noncomputable def muG (L m rm : Nat) : Measure (GSpace L m rm) :=
  gaussianPi (GIdx L m rm)

noncomputable def muZ (L rm : Nat) : Measure (ZSpace L rm) :=
  gaussianPi (ZIdx L rm)

noncomputable def muNN (L m rm : Nat) : Measure (OmegaNN L m rm) :=
  (muG L m rm).prod (muZ L rm)

/-- Gaussian matrix coordinate `B_(ell,i,j)`. -/
def BCoord {L m rm : Nat} (omega : OmegaNN L m rm)
    (ell : Fin L) (i : Fin m) (j : Fin rm) : Real :=
  omega.1 (ell, (i, j))

/-- Gaussian latent coordinate `z_(ell,j)`. -/
def zCoord {L m rm : Nat} (omega : OmegaNN L m rm) (ell : Fin L) (j : Fin rm) : Real :=
  omega.2 (ell, j)

/-- Activation coordinate `a_(ell,j) = sign(z_(ell,j))`. -/
def aCoord {L m rm : Nat} (omega : OmegaNN L m rm) (ell : Fin L) (j : Fin rm) : Real :=
  signAct (zCoord omega ell j)

/-- Realize `B` as a function extracted from an NN sample. -/
def Bfun {L m rm : Nat} (omega : OmegaNN L m rm) : Fin L -> Fin m -> Fin rm -> Real :=
  fun ell i j => BCoord omega ell i j

/-- Realize `z` as a function extracted from an NN sample. -/
def zfun {L m rm : Nat} (omega : OmegaNN L m rm) : Fin L -> Fin rm -> Real :=
  fun ell j => zCoord omega ell j

/-- Layer increment as a random vector on `OmegaNN`. -/
def DeltaH {L m rm : Nat} (ell : Fin L) : OmegaNN L m rm -> (Fin m -> Real) :=
  fun omega => deltaH (Bfun omega) (zfun omega) ell

/-- Prompt-literal name for layer increments. -/
def Δh {L m rm : Nat} (ell : Fin L) : OmegaNN L m rm -> (Fin m -> Real) :=
  DeltaH (L := L) (m := m) (rm := rm) ell

/-- Layer scalar probe as a random variable on `OmegaNN`. -/
def gProbe {L m rm : Nat} (u : EuclideanSpace Real (Fin m)) (ell : Fin L) :
    OmegaNN L m rm -> Real :=
  fun omega => gLayer (Bfun omega) (zfun omega) u ell

/-- Prompt-literal name for layer scalar probes. -/
def g {L m rm : Nat} (u : EuclideanSpace Real (Fin m)) (ell : Fin L) :
    OmegaNN L m rm -> Real :=
  gProbe (L := L) (m := m) (rm := rm) u ell

/-- Prompt-literal mean probe on `OmegaNN`: `(1/L) * sum_ell g_ell`. -/
def M_u {L m rm : Nat} (u : EuclideanSpace Real (Fin m)) : OmegaNN L m rm -> Real :=
  fun omega => meanProbe (Bfun omega) (zfun omega) u

/-- Prompt-literal averaged increment vector `W = (1/L) * sum_ell DeltaH_ell`. -/
def W {L m rm : Nat} : OmegaNN L m rm -> (Fin m -> Real) :=
  fun omega i =>
    (1 / (L : Real)) * Finset.univ.sum (fun ell : Fin L => DeltaH ell omega i)

/-- Unit sphere in `EuclideanSpace Real (Fin m)`. -/
def Sphere (m : Nat) := {u : EuclideanSpace Real (Fin m) // norm u = 1}

instance instTopologicalSpaceSphere (m : Nat) : TopologicalSpace (Sphere m) := by
  delta Sphere
  infer_instance

instance instPseudoMetricSpaceSphere (m : Nat) : PseudoMetricSpace (Sphere m) := by
  delta Sphere
  infer_instance

/-- Sphere-indexed process `X(u)(omega) = <u, W(omega)>`. -/
def X {L m rm : Nat} : Sphere m -> OmegaNN L m rm -> Real :=
  fun u omega => Finset.univ.sum (fun i : Fin m => u.1 i * W (L := L) (m := m) (rm := rm) omega i)

/-- Flattening scale appearing in the Gaussian-linear-form representation. -/
def nnScale (L rm : Nat) : Real :=
  (1 / (L : Real)) * (1 / Real.sqrt (L : Real)) * (1 / Real.sqrt (rm : Real))

/-- Flattened linear statistic over all Gaussian `B_(ell,i,j)` coordinates. -/
def M_u_fromNN {L m rm : Nat} (u : EuclideanSpace Real (Fin m))
    (omega : OmegaNN L m rm) : Real :=
  Finset.univ.sum (fun idx : GIdx L m rm =>
    nnScale L rm * u idx.2.1 *
      (BCoord omega idx.1 idx.2.1 idx.2.2 * aCoord omega idx.1 idx.2.2))

lemma M_u_eq_M_u_fromNN {L m rm : Nat} (u : EuclideanSpace Real (Fin m)) :
    M_u (L := L) (m := m) (rm := rm) u = M_u_fromNN (L := L) (m := m) (rm := rm) u := by
  funext omega
  unfold M_u meanProbe gLayer deltaH Bfun zfun activationVec
  unfold M_u_fromNN nnScale BCoord aCoord zCoord
  simp [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, mul_left_comm]

lemma M_u_eq_inner_W {L m rm : Nat} (u : EuclideanSpace Real (Fin m)) :
    M_u (L := L) (m := m) (rm := rm) u =
      fun omega => Finset.univ.sum (fun i : Fin m => u i * W (L := L) (m := m) (rm := rm) omega i) := by
  funext omega
  unfold M_u W meanProbe gLayer DeltaH
  calc
    (1 / (L : Real)) * ∑ ell, ∑ i, u i * deltaH (Bfun omega) (zfun omega) ell i
        = ∑ ell, (1 / (L : Real)) * ∑ i, u i * deltaH (Bfun omega) (zfun omega) ell i := by
            rw [Finset.mul_sum]
    _ = ∑ ell, ∑ i, (1 / (L : Real)) * (u i * deltaH (Bfun omega) (zfun omega) ell i) := by
          refine Finset.sum_congr rfl ?_
          intro ell _
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ ell, (1 / (L : Real)) * (u i * deltaH (Bfun omega) (zfun omega) ell i) := by
          rw [Finset.sum_comm]
    _ = ∑ i, u i * ((1 / (L : Real)) * ∑ ell, deltaH (Bfun omega) (zfun omega) ell i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          calc
            ∑ ell, (1 / (L : Real)) * (u i * deltaH (Bfun omega) (zfun omega) ell i)
                = ∑ ell, u i * ((1 / (L : Real)) * deltaH (Bfun omega) (zfun omega) ell i) := by
                    refine Finset.sum_congr rfl ?_
                    intro ell _
                    ring
            _ = u i * ∑ ell, (1 / (L : Real)) * deltaH (Bfun omega) (zfun omega) ell i := by
                  rw [Finset.mul_sum]
            _ = u i * ((1 / (L : Real)) * ∑ ell, deltaH (Bfun omega) (zfun omega) ell i) := by
                  congr 1
                  rw [Finset.mul_sum]

lemma M_u_eq_X {L m rm : Nat} (u : Sphere m) :
    M_u (L := L) (m := m) (rm := rm) u.1 = X (L := L) (m := m) (rm := rm) u := by
  simpa [X] using M_u_eq_inner_W (L := L) (m := m) (rm := rm) u.1

lemma M_u_sub {L m rm : Nat} (u v : EuclideanSpace Real (Fin m)) :
    (fun omega : OmegaNN L m rm =>
      M_u (L := L) (m := m) (rm := rm) u omega -
      M_u (L := L) (m := m) (rm := rm) v omega) =
    M_u (L := L) (m := m) (rm := rm) (u - v) := by
  funext omega
  have hu :
      M_u (L := L) (m := m) (rm := rm) u omega =
        M_u_fromNN (L := L) (m := m) (rm := rm) u omega := by
    simpa using congrArg (fun f => f omega) (M_u_eq_M_u_fromNN (L := L) (m := m) (rm := rm) u)
  have hv :
      M_u (L := L) (m := m) (rm := rm) v omega =
        M_u_fromNN (L := L) (m := m) (rm := rm) v omega := by
    simpa using congrArg (fun f => f omega) (M_u_eq_M_u_fromNN (L := L) (m := m) (rm := rm) v)
  have huv :
      M_u (L := L) (m := m) (rm := rm) (u - v) omega =
        M_u_fromNN (L := L) (m := m) (rm := rm) (u - v) omega := by
    simpa using
      congrArg (fun f => f omega) (M_u_eq_M_u_fromNN (L := L) (m := m) (rm := rm) (u - v))
  rw [hu, hv, huv]
  unfold M_u_fromNN
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro idx _
  change
    nnScale L rm * u.ofLp idx.2.1 * (BCoord omega idx.1 idx.2.1 idx.2.2 * aCoord omega idx.1 idx.2.2) -
      nnScale L rm * v.ofLp idx.2.1 * (BCoord omega idx.1 idx.2.1 idx.2.2 * aCoord omega idx.1 idx.2.2) =
    nnScale L rm * (u - v).ofLp idx.2.1 * (BCoord omega idx.1 idx.2.1 idx.2.2 * aCoord omega idx.1 idx.2.2)
  have hcoord : (u - v).ofLp idx.2.1 = u.ofLp idx.2.1 - v.ofLp idx.2.1 := rfl
  rw [hcoord]
  ring

lemma xId_apply (m : Nat) (i j : Fin m) :
    xId m i j = if j = i then (1 : Real) else 0 := by
  simp [xId, EuclideanSpace.single_apply]

lemma designMatrixMul_xId_apply {m : Nat}
    (theta : EuclideanSpace Real (Fin m)) (i : Fin m) :
    LeastSquares.designMatrixMul (xId m) theta i = theta i := by
  simp [LeastSquares.designMatrixMul, xId, EuclideanSpace.inner_single_right]

lemma designMatrixMul_xId_injective {m : Nat} :
    Function.Injective (LeastSquares.designMatrixMul (xId m)) := by
  intro theta1 theta2 h
  ext i
  have hcoord := congrArg (fun v => v i) h
  simpa [designMatrixMul_xId_apply] using hcoord

end

end NNGPResNet
end LeanSlt
