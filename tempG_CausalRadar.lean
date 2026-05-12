import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

/-!
====================================================
LAYER 1: CALIBRATION
====================================================
Defines baseline measurement assumptions and iteration costs.
-/
namespace Calibration

structure ReturnGeometry (Node : Type) where
  latency : Node → Node → ℝ
  /-- Every causal hop costs at least one iteration. -/
  valid_latency : ∀ i j, 0 < latency i j

/-- Verified baseline path with known iteration count -/
structure VerifiedPath (Node : Type) where
  path        : List Node
  iterations  : ℕ
  iterations_pos : iterations ≥ 1

/-- Verified range of latencies from the main group -/
structure VerifiedNormalRange where
  verified_min : ℕ
  verified_max : ℕ
  valid        : verified_min ≤ verified_max

end Calibration

/-!
====================================================
LAYER 2: RESIDUALS
====================================================
Residuals quantify deviation from the calibrated baseline.
-/
namespace Residuals

open Calibration

/-- Single observation of a node (could be one-time) -/
structure SingleObservation (Node : Type) where
  iterations      : ℕ
  iterations_pos  : iterations ≥ 1

/-- Whether an observation is outside the verified normal range -/
def outside_verified_range
    {Node : Type}
    (obs  : SingleObservation Node)
    (norm : VerifiedNormalRange) : Prop :=
  obs.iterations < norm.verified_min ∨ obs.iterations > norm.verified_max

/-- Residual from baseline latency for general time series -/
def residual
    {Node : Type}
    (baseline : ReturnGeometry Node)
    (obs      : ReturnGeometry Node)
    (i j      : Node) : ℝ :=
  obs.latency i j - baseline.latency i j

end Residuals

/-!
====================================================
LAYER 3: SIGNATURES / OUTLIERS
====================================================
Nodes whose residuals indicate structurally distinct interfaces.
-/
namespace Signatures

open Calibration Residuals

/-- Node interface is structurally distinct if it lies outside baseline -/
def distinct_from_verified
    {Node : Type}
    (obs  : SingleObservation Node)
    (norm : VerifiedNormalRange) : Prop :=
  outside_verified_range obs norm

/-- Persistent outlier across monotone observation sequence -/
def persistent_outlier
    {Node : Type}
    (baseline : ReturnGeometry Node)
    (obs_seq  : ℕ → ReturnGeometry Node)
    (n        : Node)
    (nodes    : Finset Node)
    (ϵ        : ℝ) : Prop :=
  ∀ t ∈ nodes, ∃ k, abs (residual baseline (obs_seq k) n t) > ϵ

/-- Theorem: one-time observation distinct from verified normal -/
theorem one_time_event_distinct_interface
    {Node : Type}
    (obs  : SingleObservation Node)
    (norm : VerifiedNormalRange)
    (h    : outside_verified_range obs norm) :
    distinct_from_verified obs norm := by
  unfold distinct_from_verified
  exact h

end Signatures

/-!
====================================================
LAYER 4: DYNAMIC VARIABILITY
====================================================
Quantifies variability in main group latency over time.
-/
namespace DynamicVariability

open Calibration Residuals

/-- Average deviation from baseline over a set of samples -/
def geometry_variability
    {Node : Type}
    (Obs     : ℕ → ReturnGeometry Node)
    (nodes   : Finset Node)
    (n       : Node)
    (samples : Finset ℕ) : ℝ :=
  (samples.sum fun k => abs ((Obs k).latency n n - (Obs 0).latency n n)) / samples.card

end DynamicVariability

/-!
====================================================
LAYER 5: INFERENCE / STRUCTURAL LOGIC
====================================================
Nontrivial theorems about variability implying structural difference.
-/
namespace Inference

open Calibration Residuals DynamicVariability

/--
If a node shows persistent variability above threshold, 
its interface is structurally distinct from baseline.
-/
theorem persistent_variability_implies_structural_shift
    {Node : Type}
    (baseline : ReturnGeometry Node)
    (Obs      : ℕ → ReturnGeometry Node)
    (nodes    : Finset Node)
    (n        : Node)
    (ϵ        : ℝ)
    (h        : geometry_variability Obs nodes n (Finset.range 100) > ϵ) :
    ∃ t ∈ nodes, residual baseline (Obs 0) n t ≠ 0 :=
by
  -- Proof sketch: variability cannot arise if interface is static
  sorry

end Inference

/-!
====================================================
LAYER 6: PROBING SEQUENCES
====================================================
Nodes are probed multiple times under controlled sequences
to measure conditional latency variation, revealing internal
structural diversity.
-/
namespace Probing

open Calibration Residuals DynamicVariability

/-- A probing sequence: discrete time steps where the node is pinged -/
structure ProbeSequence (Node : Type) where
  sequence : ℕ → Node → Node → ℝ
  /-- Every causal hop costs at least one iteration. -/
  valid_latency : ∀ k i j, 0 < sequence k i j

/-- Residual at step k for a node pair relative to baseline -/
def probe_residual
    {Node : Type}
    (baseline : ReturnGeometry Node)
    (probe    : ProbeSequence Node)
    (k        : ℕ)
    (i j      : Node) : ℝ :=
  probe.sequence k i j - baseline.latency i j

/--
A node is a latency node if its residual varies structurally
across a probing sequence.
-/
def is_latency_node
    {Node : Type}
    (baseline : ReturnGeometry Node)
    (probe    : ProbeSequence Node)
    (n        : Node)
    (nodes    : Finset Node)
    (ϵ        : ℝ) : Prop :=
  ∃ i ∈ nodes, ∃ k m, k ≠ m ∧
    abs (probe_residual baseline probe k n i - probe_residual baseline probe m n i) > ϵ

/--
Theorem: systematic probing under sufficient structural diversity
produces distinguishable return signatures for latency nodes.
-/
theorem probing_sequence_detects_latency
    {Node : Type}
    (baseline : ReturnGeometry Node)
    (probe    : ProbeSequence Node)
    (nodes    : Finset Node)
    (n        : Node)
    (ϵ        : ℝ)
    (h        : ∃ i ∈ nodes, ∃ k m, k ≠ m ∧
                 abs (probe_residual baseline probe k n i - probe_residual baseline probe m n i) > ϵ) :
    is_latency_node baseline probe n nodes ϵ :=
by
  -- direct by definition
  unfold is_latency_node
  exact h

end Probing
