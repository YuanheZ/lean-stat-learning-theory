import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Order.Monotone.Union

open MeasureTheory Filter Topology TopologicalSpace Set EMetric
open scoped NNReal ENNReal

/- One direction is already available in Mathlib:
lemma isCompact_closure_of_isTightMeasureSet {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) :=
-/
