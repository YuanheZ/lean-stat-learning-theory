import LeanSlt.NNGPResNet.Defs

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.longLine false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanSlt
namespace NNGPResNet

noncomputable section

def sqNN (x : Real) : NNReal :=
  Subtype.mk (x ^ 2) (sq_nonneg x)

lemma map_eval_gaussianPi
    {idxType : Type*} [Fintype idxType] [DecidableEq idxType] (i : idxType) :
    (gaussianPi idxType).map (fun w : idxType -> Real => w i) = gaussianReal 0 1 := by
  unfold gaussianPi
  exact (measurePreserving_eval (fun _ : idxType => gaussianReal 0 1) i).map_eq

lemma map_scaled_coord_eq_gaussianPi
    {idxType : Type*} [Fintype idxType] [DecidableEq idxType]
    (a : idxType -> Real) (i : idxType) :
    (gaussianPi idxType).map (fun w : idxType -> Real => a i * w i) =
      gaussianReal 0 (sqNN (a i)) := by
  have hMapMap :
      (gaussianPi idxType).map (fun w : idxType -> Real => a i * w i) =
        ((gaussianPi idxType).map (fun w : idxType -> Real => w i)).map
          (fun x : Real => a i * x) := by
    rw [Measure.map_map (measurable_const_mul (a i)) (measurable_pi_apply i)]
    rfl
  calc
    (gaussianPi idxType).map (fun w : idxType -> Real => a i * w i)
        = ((gaussianPi idxType).map (fun w : idxType -> Real => w i)).map
            (fun x : Real => a i * x) := hMapMap
    _ = (gaussianReal 0 1).map (fun x : Real => a i * x) := by
          rw [map_eval_gaussianPi i]
    _ = gaussianReal (a i * 0)
          (sqNN (a i) * (1 : NNReal)) := by
          simpa using
            (gaussianReal_map_const_mul
              (μ := (0 : Real)) (v := (1 : NNReal)) (c := a i))
    _ = gaussianReal 0 (sqNN (a i)) := by simp [sqNN]

lemma map_linear_sum_finset_eq_gaussianPi
    {idxType : Type*} [Fintype idxType] [DecidableEq idxType]
    (a : idxType -> Real) (s : Finset idxType) :
    (gaussianPi idxType).map
        (fun w : idxType -> Real => Finset.sum s (fun j => a j * w j)) =
      gaussianReal 0 (Finset.sum s (fun j => sqNN (a j))) := by
  classical
  haveI : IsProbabilityMeasure (gaussianPi idxType) := by
    unfold gaussianPi
    infer_instance
  induction s using Finset.induction_on with
  | empty =>
      simp [Measure.map_const, gaussianReal_zero_var]
  | @insert i s hi ih =>
      let xFn : (idxType -> Real) -> Real :=
        Finset.sum s (fun j : idxType => fun w : idxType -> Real => a j * w j)
      let yFn : (idxType -> Real) -> Real :=
        fun w => a i * w i
      have hIIndepEval :
          iIndepFun (fun j : idxType => fun w : idxType -> Real => w j)
            (gaussianPi idxType) := by
        unfold gaussianPi
        exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
      have hIIndep :
          iIndepFun (fun j : idxType => fun w : idxType -> Real => a j * w j)
            (gaussianPi idxType) := by
        exact hIIndepEval.comp (fun j => fun x : Real => a j * x)
          (fun j => measurable_const_mul (a j))
      have hMeas :
          forall j : idxType,
            Measurable (fun w : idxType -> Real => a j * w j) := by
        intro j
        exact (measurable_const_mul (a j)).comp (measurable_pi_apply j)
      have hIndep : IndepFun xFn yFn (gaussianPi idxType) := by
        dsimp [xFn, yFn]
        exact hIIndep.indepFun_finset_sum_of_notMem hMeas hi
      have hXeq :
          xFn = (fun w : idxType -> Real => Finset.sum s (fun j => a j * w j)) := by
        funext w
        simp [xFn, Finset.sum_apply]
      have ihX :
          (gaussianPi idxType).map xFn =
            gaussianReal 0 (Finset.sum s (fun j => sqNN (a j))) := by
        simpa [hXeq] using ih
      have hFun :
          (fun w : idxType -> Real =>
              Finset.sum (insert i s) (fun j => a j * w j)) = xFn + yFn := by
        funext w
        simp [xFn, yFn, Finset.sum_insert, hi, add_comm]
      calc
        (gaussianPi idxType).map
            (fun w : idxType -> Real =>
              Finset.sum (insert i s) (fun j => a j * w j))
            = (gaussianPi idxType).map (xFn + yFn) := by
                rw [hFun]
        _ = gaussianReal (0 + 0)
              (Finset.sum s (fun j => sqNN (a j)) + sqNN (a i)) := by
              exact gaussianReal_add_gaussianReal_of_indepFun hIndep ihX
                (map_scaled_coord_eq_gaussianPi a i)
        _ = gaussianReal 0
              (Finset.sum (insert i s) (fun j => sqNN (a j))) := by
              simp [Finset.sum_insert, hi, add_comm, sqNN]

theorem map_linear_sum_gaussianPi_eq_gaussian
    {idxType : Type*} [Fintype idxType] [DecidableEq idxType]
    (a : idxType -> Real) :
    (gaussianPi idxType).map
        (fun w : idxType -> Real => Finset.univ.sum (fun i => a i * w i)) =
      gaussianReal 0 (Finset.univ.sum (fun i => sqNN (a i))) := by
  simpa using map_linear_sum_finset_eq_gaussianPi (a := a) (s := Finset.univ)

lemma measurable_signAct : Measurable signAct := by
  unfold signAct
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const measurable_id

lemma signAct_sq (x : Real) : signAct x ^ 2 = 1 := by
  by_cases hx : 0 <= x <;> simp [signAct, hx]

def coeffNNWithSign {L m rm : Nat}
    (t : EuclideanSpace Real (Fin m))
    (zv : ZSpace L rm)
    (idx : GIdx L m rm) : Real :=
  nnScale L rm * t idx.2.1 * signAct (zv (idx.1, idx.2.2))

def linearProbeGWithSign {L m rm : Nat}
    (t : EuclideanSpace Real (Fin m))
    (zv : ZSpace L rm)
    (g : GSpace L m rm) : Real :=
  Finset.univ.sum
    (fun idx : GIdx L m rm => coeffNNWithSign (L := L) (rm := rm) t zv idx * g idx)

lemma M_u_fromNN_eq_linearProbeGWithSign
    {L m rm : Nat} (t : EuclideanSpace Real (Fin m)) :
    M_u_fromNN (L := L) (m := m) (rm := rm) t =
      fun omega : OmegaNN L m rm =>
        linearProbeGWithSign (L := L) (rm := rm) t omega.2 omega.1 := by
  funext omega
  unfold M_u_fromNN linearProbeGWithSign coeffNNWithSign BCoord aCoord zCoord
  refine Finset.sum_congr rfl ?_
  intro idx _
  ring

lemma measurable_linearProbeGWithSign
    {L m rm : Nat} (t : EuclideanSpace Real (Fin m)) (zv : ZSpace L rm) :
    Measurable (linearProbeGWithSign (L := L) (rm := rm) t zv) := by
  unfold linearProbeGWithSign
  refine Finset.measurable_sum (s := (Finset.univ : Finset (GIdx L m rm))) ?_
  intro idx _
  exact ((measurable_const_mul (coeffNNWithSign (L := L) (rm := rm) t zv idx)).comp
    (measurable_pi_apply idx))

lemma measurable_M_u_fromNN
    {L m rm : Nat} (t : EuclideanSpace Real (Fin m)) :
    Measurable (M_u_fromNN (L := L) (m := m) (rm := rm) t) := by
  unfold M_u_fromNN
  refine Finset.measurable_sum (s := (Finset.univ : Finset (GIdx L m rm))) ?_
  intro idx _
  have hB :
      Measurable (fun omega : OmegaNN L m rm => BCoord omega idx.1 idx.2.1 idx.2.2) := by
    unfold BCoord
    exact (measurable_pi_apply idx).comp measurable_fst
  have hA : Measurable (fun omega : OmegaNN L m rm => aCoord omega idx.1 idx.2.2) := by
    unfold aCoord zCoord
    exact measurable_signAct.comp ((measurable_pi_apply (idx.1, idx.2.2)).comp measurable_snd)
  exact ((measurable_const_mul (nnScale L rm * t idx.2.1)).comp (hB.mul hA))

lemma measurable_M_u
    {L m rm : Nat} (t : EuclideanSpace Real (Fin m)) :
    Measurable (M_u (L := L) (m := m) (rm := rm) t) := by
  simpa [M_u_eq_M_u_fromNN (L := L) (m := m) (rm := rm) t] using
    measurable_M_u_fromNN (L := L) (m := m) (rm := rm) t

lemma map_linearProbeGWithSign_gaussian
    {L m rm : Nat} (t : EuclideanSpace Real (Fin m)) (zv : ZSpace L rm) :
    (muG L m rm).map (linearProbeGWithSign (L := L) (rm := rm) t zv) =
      gaussianReal 0
        (Finset.univ.sum
          (fun idx : GIdx L m rm => sqNN (coeffNNWithSign (L := L) (rm := rm) t zv idx))) := by
  simpa [muG, linearProbeGWithSign, coeffNNWithSign]
    using map_linear_sum_gaussianPi_eq_gaussian
      (a := coeffNNWithSign (L := L) (rm := rm) t zv)

lemma sum_t_sq_repeated
    {L m rm : Nat} (t : EuclideanSpace Real (Fin m)) :
    Finset.univ.sum (fun idx : GIdx L m rm => (t idx.2.1) ^ 2)
      = (L : Real) * (rm : Real) * Finset.univ.sum (fun i : Fin m => (t i) ^ 2) := by
  simp [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

lemma sum_sq_eq_norm_sq {m : Nat} (t : EuclideanSpace Real (Fin m)) :
    Finset.univ.sum (fun i : Fin m => (t i) ^ 2) = norm t ^ 2 := by
  have hEuclid :
      norm t ^ 2 = Finset.univ.sum (fun i : Fin m => norm (t i) ^ 2) := by
    simpa using (EuclideanSpace.norm_sq_eq t)
  have hCoord :
      Finset.univ.sum (fun i : Fin m => norm (t i) ^ 2)
        = Finset.univ.sum (fun i : Fin m => (t i) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Real.norm_eq_abs, sq_abs]
  linarith

lemma coeff_variance_eq_norm_sq_withSign
    {L m rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (t : EuclideanSpace Real (Fin m)) (zv : ZSpace L rm) :
    (Finset.univ.sum
      (fun idx : GIdx L m rm => sqNN (coeffNNWithSign (L := L) (rm := rm) t zv idx)) : Real)
      = norm t ^ 2 / (L : Real) ^ 2 := by
  have hL0 : Ne (L : Real) 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hrm0 : Ne (rm : Real) 0 := by exact_mod_cast (Nat.ne_of_gt hrm)
  calc
    (Finset.univ.sum
      (fun idx : GIdx L m rm => sqNN (coeffNNWithSign (L := L) (rm := rm) t zv idx)) : Real)
        = Finset.univ.sum
            (fun idx : GIdx L m rm => (coeffNNWithSign (L := L) (rm := rm) t zv idx) ^ 2) := by
            simp [sqNN]
    _ = Finset.univ.sum
          (fun idx : GIdx L m rm =>
            (nnScale L rm) ^ 2 * (t idx.2.1) ^ 2 * (signAct (zv (idx.1, idx.2.2)) ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro idx _
          unfold coeffNNWithSign
          ring
    _ = Finset.univ.sum
          (fun idx : GIdx L m rm => (nnScale L rm) ^ 2 * (t idx.2.1) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro idx _
          simp [signAct_sq]
    _ = (nnScale L rm) ^ 2 * Finset.univ.sum (fun idx : GIdx L m rm => (t idx.2.1) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (nnScale L rm) ^ 2 *
          ((L : Real) * (rm : Real) * Finset.univ.sum (fun i : Fin m => (t i) ^ 2)) := by
          rw [sum_t_sq_repeated]
    _ = (nnScale L rm) ^ 2 * ((L : Real) * (rm : Real) * norm t ^ 2) := by
          rw [sum_sq_eq_norm_sq]
    _ = norm t ^ 2 / (L : Real) ^ 2 := by
          have hLReal : (0 : Real) < (L : Real) := by exact_mod_cast hL
          have hrmReal : (0 : Real) < (rm : Real) := by exact_mod_cast hrm
          have hsqrtL0 : Ne (Real.sqrt (L : Real)) 0 := by
            exact ne_of_gt (Real.sqrt_pos.mpr hLReal)
          have hsqrtrm0 : Ne (Real.sqrt (rm : Real)) 0 := by
            exact ne_of_gt (Real.sqrt_pos.mpr hrmReal)
          have hLsq : (Real.sqrt (L : Real)) ^ 2 = (L : Real) := by
            nlinarith [Real.sq_sqrt (show (0 : Real) <= (L : Real) by positivity)]
          have hrmsq : (Real.sqrt (rm : Real)) ^ 2 = (rm : Real) := by
            nlinarith [Real.sq_sqrt (show (0 : Real) <= (rm : Real) by positivity)]
          unfold nnScale
          field_simp [hL0, hrm0, hsqrtL0, hsqrtrm0]
          rw [hLsq, hrmsq]

def vecVarNN (L : Nat) {m : Nat} (t : EuclideanSpace Real (Fin m)) : NNReal :=
  Subtype.mk (norm t ^ 2 / (L : Real) ^ 2) (by positivity)

lemma map_linearProbeGWithSign_gaussian_normSq
    {L m rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (t : EuclideanSpace Real (Fin m)) (zv : ZSpace L rm) :
    (muG L m rm).map (linearProbeGWithSign (L := L) (rm := rm) t zv) =
      gaussianReal 0 (vecVarNN L t) := by
  have hMap := map_linearProbeGWithSign_gaussian (L := L) (m := m) (rm := rm) t zv
  have hVar :
      (Finset.univ.sum
        (fun idx : GIdx L m rm => sqNN (coeffNNWithSign (L := L) (rm := rm) t zv idx)) : Real)
        = norm t ^ 2 / (L : Real) ^ 2 :=
    coeff_variance_eq_norm_sq_withSign (L := L) (m := m) (rm := rm) hL hrm t zv
  calc
    (muG L m rm).map (linearProbeGWithSign (L := L) (rm := rm) t zv)
        = gaussianReal 0
            (Finset.univ.sum
              (fun idx : GIdx L m rm => sqNN (coeffNNWithSign (L := L) (rm := rm) t zv idx))) := hMap
    _ = gaussianReal 0 (vecVarNN L t) := by
          apply congrArg (gaussianReal 0)
          apply Subtype.ext
          simpa [vecVarNN] using hVar

theorem map_M_u_fromNN_gaussian_any
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (t : EuclideanSpace Real (Fin m)) :
    (muNN L m rm).map (M_u_fromNN (L := L) (m := m) (rm := rm) t)
      = gaussianReal 0 (vecVarNN L t) := by
  haveI : SFinite (muZ L rm) := by
    unfold muZ gaussianPi
    infer_instance
  haveI : SFinite (muG L m rm) := by
    unfold muG gaussianPi
    infer_instance
  have hMeasM : Measurable (M_u_fromNN (L := L) (m := m) (rm := rm) t) :=
    measurable_M_u_fromNN (L := L) (m := m) (rm := rm) t
  ext s hs
  let pre := Set.preimage (M_u_fromNN (L := L) (m := m) (rm := rm) t) s
  have hPre : MeasurableSet pre := hMeasM hs
  calc
    ((muNN L m rm).map (M_u_fromNN (L := L) (m := m) (rm := rm) t)) s
        = (muNN L m rm) pre := by
            simpa [pre] using Measure.map_apply hMeasM hs
    _ = lintegral (muZ L rm) (fun zv : ZSpace L rm =>
          (muG L m rm)
            (Set.preimage (fun g : GSpace L m rm => (g, zv)) pre)) := by
          unfold muNN
          simpa [pre] using Measure.prod_apply_symm hPre
    _ = lintegral (muZ L rm) (fun _ : ZSpace L rm => (gaussianReal 0 (vecVarNN L t)) s) := by
          refine lintegral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro zv
          have hMapZ := map_linearProbeGWithSign_gaussian_normSq
            (L := L) (m := m) (rm := rm) hL hrm t zv
          have hMeasZ : Measurable (linearProbeGWithSign (L := L) (rm := rm) t zv) :=
            measurable_linearProbeGWithSign (L := L) (m := m) (rm := rm) t zv
          have hSetEq :
              Set.preimage (fun g : GSpace L m rm => (g, zv)) pre =
                Set.preimage (linearProbeGWithSign (L := L) (rm := rm) t zv) s := by
            ext g
            simp [pre, M_u_fromNN_eq_linearProbeGWithSign]
          calc
            (muG L m rm) (Set.preimage (fun g : GSpace L m rm => (g, zv)) pre)
                = (muG L m rm)
                    (Set.preimage (linearProbeGWithSign (L := L) (rm := rm) t zv) s) := by
                      rw [hSetEq]
            _ = ((muG L m rm).map (linearProbeGWithSign (L := L) (rm := rm) t zv)) s := by
                  symm
                  exact Measure.map_apply hMeasZ hs
            _ = (gaussianReal 0 (vecVarNN L t)) s := by
                  simpa using congrArg (fun nu => nu s) hMapZ
    _ = (gaussianReal 0 (vecVarNN L t)) s := by
          haveI : IsProbabilityMeasure (muZ L rm) := by
            unfold muZ gaussianPi
            infer_instance
          simp

theorem map_M_u_gaussian_any
    {m L rm : Nat} (hL : 0 < L) (hrm : 0 < rm)
    (t : EuclideanSpace Real (Fin m)) :
    (muNN L m rm).map (M_u (L := L) (m := m) (rm := rm) t)
      = gaussianReal 0 (vecVarNN L t) := by
  simpa [M_u_eq_M_u_fromNN (L := L) (m := m) (rm := rm) t] using
    map_M_u_fromNN_gaussian_any (m := m) (L := L) (rm := rm) hL hrm t

lemma sum_sq_eq_one_of_unit {m : Nat}
    (u : EuclideanSpace Real (Fin m)) (hu : norm u = 1) :
    Finset.univ.sum (fun i : Fin m => (u i) ^ 2) = 1 := by
  have hNormSq : norm u ^ 2 = 1 := by
    nlinarith [hu]
  have hEq := sum_sq_eq_norm_sq u
  linarith

end

end NNGPResNet
end LeanSlt
