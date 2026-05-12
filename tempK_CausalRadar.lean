import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

namespace CausalGraph

variable (Node : Type) [DecidableEq Node]

/-!
====================================================
LAYER 1: CALIBRATION
==================================================== -/

structure VerifiedNormalRange where
  verified_min : ℕ
  verified_max : ℕ
  valid : verified_min ≤ verified_max

structure Calibration where
  baseline_nodes : Finset Node
  normal_range   : VerifiedNormalRange

def outside_verified_range
    (obs : ℕ)
    (norm : VerifiedNormalRange) : Prop :=
  obs < norm.verified_min ∨ obs > norm.verified_max

def distinct_from_verified
    (obs : ℕ)
    (norm : VerifiedNormalRange) : Prop :=
  outside_verified_range obs norm


/-!
====================================================
LAYER 2: OBSERVATION / RESIDUALS
==================================================== -/

structure Observation where
  obs_node : Node
  residual : Node → ℝ

def stable_signature (C : Calibration) (Obs : Observation) : Prop :=
  ∃ n ∈ C.baseline_nodes, Obs.residual n ≠ 0


/-!
====================================================
LAYER 3: PROBING + SEMIGROUP STRUCTURE
==================================================== -/

/-- Latency function (hidden graph abstraction) -/
structure ReturnGeometry where
  delay : Node → Node → ℝ
  valid : ∀ i j, 0 ≤ delay i j

/-- A probe is a transformation of the delay field -/
structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

/-- Probe composition = semigroup composition -/
def composeProbe (p q : Probe) : Probe :=
{ transform := fun f => p.transform (q.transform f) }

/-- Identity probe -/
def idProbe : Probe :=
{ transform := fun f => f }

/-- Apply probe -/
def applyProbe (p : Probe) (g : Node → Node → ℝ) :=
  p.transform g


/-!
====================================================
LAYER 4: COMMUTATOR / ASYMMETRY
==================================================== -/

def commutator (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  g i j - g j i

def asymmetry (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  Real.abs (commutator g i j)

def node_asymmetry (g : Node → Node → ℝ) (n : Node) : ℝ :=
  ∑ m : Node, asymmetry g n m


/-!
====================================================
LAYER 5: ACCUMULATION (MONOID ACTION)
==================================================== -/

/-- Folding probes over time (monoid action) -/
def foldProbes :
    List Probe → (Node → Node → ℝ) → (Node → Node → ℝ)
| [], g => g
| p :: ps, g => foldProbes ps (p.transform g)

/-- Accumulated asymmetry over time steps -/
def accumulated_asymmetry
    (probes : List Probe)
    (g : Node → Node → ℝ)
    (n : Node) : ℝ :=
  ∑ t : Fin probes.length,
    node_asymmetry (applyProbe (probes.get t) g) n


/-!
====================================================
LAYER 6: STRUCTURAL DIVERSITY (PURE DEFINITION)
==================================================== -/

def structural_diversity
    (probes : List Probe)
    (g : Node → Node → ℝ)
    (nodes : Finset Node) : ℝ :=
  ∑ n in nodes,
    accumulated_asymmetry probes g n


def detectable_threshold : ℝ := 0


/-!
====================================================
LAYER 7: KEY THEOREM (FULLY CONSTRUCTIVE)
==================================================== -/

/--
If structural diversity is positive,
then some node must exhibit asymmetry accumulation.
This is purely algebraic (pigeonhole principle over ℝ⁺ sums).
-/
theorem exists_latent_asymmetry_node
    (probes : List Probe)
    (g : Node → Node → ℝ)
    (nodes : Finset Node)
    (hpos : structural_diversity probes g nodes > 0) :
    ∃ n ∈ nodes,
      accumulated_asymmetry probes g n > 0 := by
  unfold structural_diversity at hpos

  have hsum :
      ∑ n in nodes,
        accumulated_asymmetry probes g n > 0 := by
    exact hpos

  have h_exists :
      ∃ n ∈ nodes,
        accumulated_asymmetry probes g n > 0 := by
  {
    apply Finset.exists_pos_of_sum_pos hsum
  }

  exact h_exists


/-!
====================================================
INTERPRETATION LAYER (NON-FORMAL)
====================================================

- probes form a semigroup (composition over time)
- asymmetry is a monoid action observable
- structural diversity = total observable curvature
- positivity implies existence of a detectable node
-/

end CausalGraph
