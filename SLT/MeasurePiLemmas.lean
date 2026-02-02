import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory

theorem pi_map_eval {ι: Type*} {Ω : ι → Type*} [Fintype ι] [DecidableEq ι]
  [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
  [∀ i, IsProbabilityMeasure (μ i)] (k : ι): (Measure.pi μ).map (Function.eval k) = (μ k) := by
  apply Measure.ext_iff.mpr
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply k) hs, Set.eval_preimage, Measure.pi_pi]
  calc
    _ = ∏ i, if i = k then μ k s else 1 := by
      congr
      ext _
      split
      next h =>
        subst h
        simp_all only [Function.update_self]
      next h => simp_all only [ne_eq, not_false_eq_true, Function.update_of_ne, measure_univ]
    _ = _ := by
      exact Fintype.prod_ite_eq' k fun j ↦ μ k s

variable {Ω ι: Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]

theorem pi_eval_iIndepFun :
  iIndepFun Function.eval (Measure.pi fun _ ↦ μ : Measure (ι → Ω)) := by
  simp only [iIndepFun, Kernel.iIndepFun, Kernel.iIndep, Kernel.iIndepSets, Set.mem_setOf_eq,
    Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
  intro s f hf
  simp only [MeasurableSet, MeasurableSpace.comap] at hf
  let f' := fun (i : ι) (hi : i ∈ s) ↦ Classical.choose (hf i hi)
  let hf' := fun (i : ι) (hi : i ∈ s) ↦ Classical.choose_spec (hf i hi)
  let f'' := fun (i : ι) ↦ if h : i ∈ s then f' i h else Set.univ
  have : (⋂ i ∈ s, f i) = Set.univ.pi f'' := by
    ext x
    constructor
    · intro hx i _
      dsimp [f'']
      if h : i ∈ s then
        rw [dif_pos h]
        have := Set.mem_iInter.mp hx i
        have := Set.mem_iInter.mp this h
        rw [←(hf' i h).2] at this
        exact this
      else
        rw [dif_neg h]
        trivial
    · intro hx
      apply Set.mem_iInter.mpr
      intro i
      apply Set.mem_iInter.mpr
      intro hi
      have := hx i trivial
      dsimp [f''] at this
      rw [dif_pos hi] at this
      rw [←(hf' i hi).2]
      exact this
  rw [this, Measure.pi_pi]
  calc
    _ = ∏ i : ι, if i ∈ s then (Measure.pi fun x ↦ μ) (f i) else 1 := by
      congr
      ext i
      dsimp only [f'']
      if h : i ∈ s then
        rw [dif_pos h, if_pos h, ←(hf' i h).2]
        dsimp [f']
        rw [←Measure.map_apply]
        · congr
          apply Eq.symm
          exact pi_map_eval i
        · exact measurable_pi_apply i
        · exact (hf' i h).1
      else
        rw [dif_neg h, if_neg h]
        exact isProbabilityMeasure_iff.mp inferInstance
    _ = _ := Fintype.prod_ite_mem s fun i ↦ (Measure.pi fun x ↦ μ) (f i)

theorem pi_comp_eval_iIndepFun {𝓧 : Type*} [MeasurableSpace 𝓧] {X : Ω → 𝓧} (hX : Measurable X):
  iIndepFun (fun (i : ι) ↦ X ∘ (Function.eval i)) (Measure.pi fun _ ↦ μ) := by
  apply iIndepFun.comp pi_eval_iIndepFun _ (fun _ ↦ hX)
