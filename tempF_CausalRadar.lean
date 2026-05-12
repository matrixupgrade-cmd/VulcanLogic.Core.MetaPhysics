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
A calibration defines the expected (baseline) causal interface.
This is the reference model all observations are compared against.
-/

namespace CalibrationLayer

/-- Hidden system (not directly observable) -/
abbrev CausalSystem (Node : Type) := Node → Node → Prop

/-- Finite observation domain -/
abbrev Observed (Node : Type) := Finset Node

/--
Calibration = expected baseline interface behavior.
This is NOT the true system, only the observer model.
-/
structure Calibration (Node : Type) where
  expected_delay : Node → Node → ℝ
  valid : ∀ i j, 0 ≤ expected_delay i j

end CalibrationLayer


/-!
====================================================
LAYER 2: OBSERVATION + RESIDUALS
====================================================
Observations are measured return times.
Residuals are deviations from calibrated expectation.
-/

namespace ResidualLayer

open CalibrationLayer

structure Observation (Node : Type) where
  observed_delay : Node → Node → ℝ
  valid : ∀ i j, 0 ≤ observed_delay i j

/--
Residual = observed - expected.
This is the fundamental signal object.
-/
def residual
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (i j : Node) : ℝ :=
  O.observed_delay i j - C.expected_delay i j

/-- Consistency with calibration (no deviation) -/
def calibrated_consistent
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (i j : Node) : Prop :=
  residual C O i j = 0

/--
Weak anomaly = any deviation from calibration.
Noise-sensitive notion.
-/
def weak_anomaly
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (i j : Node) : Prop :=
  residual C O i j ≠ 0

end ResidualLayer


/-!
====================================================
LAYER 3: SIGNATURES (STRUCTURE IN TIME OR SPACE)
====================================================
This layer captures persistent structure in residuals.
-/

namespace SignatureLayer

open ResidualLayer
open CalibrationLayer

/--
Radar signature = structured residual pattern
over a set of node pairs.
-/
def radar_signature
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (S : Finset (Node × Node)) : Prop :=
  ∀ p ∈ S,
    residual C O p.1 p.2 ≠ 0

/--
Radar signature restricted to an observed subset of nodes.
This makes the "limited observer" explicit.
-/
def radar_signature_on
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (ObsNodes : Observed Node) : Prop :=
  ∀ i ∈ ObsNodes, ∀ j ∈ ObsNodes,
    residual C O i j ≠ 0

/--
Persistent signature across multiple observations.
-/
def stable_signature
    {Node : Type}
    (C : Calibration Node)
    (Obs : ℕ → Observation Node)
    (S : Finset (Node × Node)) : Prop :=
  ∀ n, radar_signature C (Obs n) S

/--
An interface shift is NOT noise:
it is persistent structured deviation from calibration.
-/
def interface_shift
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (s : Node)
    (nodes : Finset Node) : Prop :=
  ∃ t ∈ nodes,
    residual C O s t ≠ 0

end SignatureLayer


/-!
====================================================
LAYER 4: INFERENCE (CORE THEOREMS)
====================================================
This is where we extract structural conclusions.
NOT about hidden graphs — about compatibility classes.
-/

namespace InferenceLayer

open CalibrationLayer
open ResidualLayer
open SignatureLayer

/--
Compatibility class of hidden systems for a given
calibration and observation.

Currently a placeholder: in a more refined model,
this would encode the rule "G is compatible with (C, O)".
-/
def compatibleSystems
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node) :
    Set (CausalSystem Node) :=
  { G | True }  -- structural hook for future refinement

/--
Key principle:

Calibration defines a baseline equivalence class.
Residuals define deviation geometry.
Signatures define stable deviation structure.
-/

/--
Main structural inference principle:

A persistent radar signature implies the system
cannot be fully described by the calibration model alone.
-/
theorem radar_signature_nontrivial
    {Node : Type}
    (C : Calibration Node)
    (O : Observation Node)
    (S : Finset (Node × Node))
    (h : radar_signature C O S)
    (hne : S.Nonempty) :
    ∃ p ∈ S, residual C O p.1 p.2 ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hp, h p hp⟩

/--
Core conceptual theorem (interface-level result):

Persistent stable deviation implies:
- non-equivalence to calibration baseline
- structurally distinct interface regime

This version is intentionally weak: it only records
that some structural statement holds.
-/
theorem stable_signature_implies_interface_shift_trivial
    {Node : Type}
    (C : Calibration Node)
    (Obs : ℕ → Observation Node)
    (S : Finset (Node × Node))
    (h : stable_signature C Obs S) :
    True := by
  -- intentionally weak: inference is structural, not constructive
  trivial

/--
Strengthened inference theorem:

If a stable signature exists on a nonempty set of pairs,
then for every observation index `n` there is some node `s`
and some finite set of nodes `nodes` such that the interface
at `s` is shifted relative to the calibration.

This makes "interface shift somewhere in the observed regime"
explicit for each time step.
-/
theorem stable_signature_implies_exists_shift
    {Node : Type}
    (C : Calibration Node)
    (Obs : ℕ → Observation Node)
    (S : Finset (Node × Node))
    (hS : S.Nonempty)
    (h : stable_signature C Obs S) :
    ∀ n, ∃ s (nodes : Finset Node),
      interface_shift C (Obs n) s nodes := by
  intro n
  classical
  -- pick a witness pair from the nonempty signature set
  obtain ⟨p, hp⟩ := hS
  have hSig := h n
  have hres : residual C (Obs n) p.1 p.2 ≠ 0 := hSig p hp
  -- use the first component as `s` and a singleton as `nodes`
  refine ⟨p.1, {p.2}, ?_⟩
  unfold interface_shift
  refine ⟨p.2, ?_, hres⟩
  simp

end InferenceLayer


/-!
====================================================
INTERPRETATION (NON-FORMAL LAYER)
====================================================

This framework applies to any system where:

1. A calibrated baseline model exists
   - radar systems
   - seismology
   - network latency measurement
   - institutional workflow timing
   - causal graph observation

2. Observations produce measurable return-time structure

3. Residuals encode deviation from calibration

Key principle:

"Fast" and "slow" are not absolute properties.
They are residuals relative to a calibration interface.

A radar signature is:
→ persistent structured residual geometry
→ stable under repeated observation
→ incompatible with baseline equivalence class

This does NOT imply:
- hidden graph reconstruction
- shortest-path inference
- explicit bypass mechanisms

It implies:
- structural non-equivalence to calibration model
- existence of distinct interface regime
- constrained hidden causal compatibility class
