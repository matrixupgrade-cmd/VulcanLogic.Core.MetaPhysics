```lean id="83vb9r"
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Defs
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

/-!
======================================================
INTERFACE CONFIGURATION GEOMETRY
------------------------------------------------------

Core intuition:

  Two hidden graph systems communicate through a
  junction boundary.

  A Probe transforms the hidden latency field.

  Different interface configurations produce different
  observable distortions at the junction.

  However:

    probes cannot invent fundamentally new observable
    distinctions beyond the asymmetry structure already
    present in the hidden field.

  Therefore:

    low asymmetry diversity in the hidden field forces
    collapse of the effective optimization geometry.

This file formalizes:

  * observable equivalence
  * signal entropy
  * observable complexity
  * representative subspaces
  * complexity collapse sketches

The entropy notion here is structural/combinatorial,
NOT probabilistic.

======================================================
-/

namespace InterfaceConfig

-- ==================================================
-- BASIC STRUCTURES
-- ==================================================

variable (Node : Type) [DecidableEq Node]

structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

def applyProbe
    (p : Probe Node)
    (g : Node → Node → ℝ) :
    Node → Node → ℝ :=
  p.transform g

def commutator
    (g   : Node → Node → ℝ)
    (i j : Node) : ℝ :=
  g i j - g j i

def asymmetry
    (g   : Node → Node → ℝ)
    (i j : Node) : ℝ :=
  Real.abs (commutator g i j)

def node_asymmetry
    (g     : Node → Node → ℝ)
    (nodes : Finset Node)
    (n     : Node) : ℝ :=
  ∑ m in nodes, asymmetry g n m

-- ==================================================
-- INTERFACE GEOMETRY
-- ==================================================

structure Junction where
  nodes : Finset Node

abbrev InterfaceConfig := Probe Node

abbrev ConfigSpace := List (InterfaceConfig Node)

def config_count
    (cs : ConfigSpace Node) : ℕ :=
  cs.length

-- ==================================================
-- DISTORTION
-- ==================================================

def interface_distortion
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℝ :=
  ∑ n in junc.nodes,
    node_asymmetry Node
      (applyProbe Node cfg g)
      junc.nodes
      n

theorem interface_distortion_nonneg
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) :
    0 ≤ interface_distortion Node cfg g junc := by
  unfold interface_distortion
  unfold node_asymmetry
  unfold asymmetry
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro m hm
  exact Real.abs_nonneg _

-- ==================================================
-- OBSERVATIONAL EQUIVALENCE
-- ==================================================

/-!
Two interface configurations are observationally
equivalent if the junction cannot distinguish them
through distortion measurements.
-/

def observationally_equivalent
    (cfg₁ cfg₂ : InterfaceConfig Node)
    (g          : Node → Node → ℝ)
    (junc       : Junction Node) : Prop :=

  interface_distortion Node cfg₁ g junc =
  interface_distortion Node cfg₂ g junc

theorem observationally_equivalent_refl
    (cfg : InterfaceConfig Node)
    (g   : Node → Node → ℝ)
    (junc : Junction Node) :
    observationally_equivalent
      Node cfg cfg g junc := by
  unfold observationally_equivalent

theorem observationally_equivalent_symm
    (cfg₁ cfg₂ : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) :
    observationally_equivalent
      Node cfg₁ cfg₂ g junc →
    observationally_equivalent
      Node cfg₂ cfg₁ g junc := by
  intro h
  unfold observationally_equivalent at *
  exact Eq.symm h

theorem observationally_equivalent_trans
    (cfg₁ cfg₂ cfg₃ : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) :
    observationally_equivalent
      Node cfg₁ cfg₂ g junc →
    observationally_equivalent
      Node cfg₂ cfg₃ g junc →
    observationally_equivalent
      Node cfg₁ cfg₃ g junc := by
  intro h₁ h₂
  unfold observationally_equivalent at *
  exact Eq.trans h₁ h₂

-- ==================================================
-- ASYMMETRY IMAGE GEOMETRY
-- ==================================================

/-!
The asymmetry image is the set of distinct asymmetry
values observable across the junction boundary.

This acts as a structural entropy source.
-/

def asymmetry_values
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : List ℝ :=

  ((junc.nodes.product junc.nodes).val).map
    (fun p =>
      asymmetry g p.1 p.2)

def distinct_asymmetry_values
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : Finset ℝ :=

  (asymmetry_values Node g junc).toFinset

/-- Structural entropy of the hidden latency field. -/
def signal_entropy
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=

  (distinct_asymmetry_values
    Node g junc).card

-- ==================================================
-- OBSERVABLE COMPLEXITY
-- ==================================================

/-!
Observable complexity measures the number of distinct
distortion outputs achievable by the configuration
space.

This is the effective observable geometry seen at the
junction.
-/

def distortion_values
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : List ℝ :=

  cs.map (fun cfg =>
    interface_distortion Node cfg g junc)

def distinct_distortion_values
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : Finset ℝ :=

  (distortion_values Node cs g junc).toFinset

def observable_complexity
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=

  (distinct_distortion_values
    Node cs g junc).card

-- ==================================================
-- MINIMAL CONFIGURATIONS
-- ==================================================

def is_minimal_config
    (cs   : ConfigSpace Node)
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : Prop :=

  cfg ∈ cs ∧
  ∀ cfg' ∈ cs,
    interface_distortion Node cfg g junc ≤
    interface_distortion Node cfg' g junc

-- ==================================================
-- REPRESENTATIVE SUBSPACES
-- ==================================================

/-!
A representative subspace chooses one representative
configuration for each observable distortion value.

Optimization can therefore occur over representatives
instead of the full raw configuration space.
-/

def representative_subspace
    (reps : ConfigSpace Node)
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : Prop :=

  (∀ cfg ∈ reps, cfg ∈ cs) ∧

  (∀ d ∈ distinct_distortion_values
      Node cs g junc,
    ∃ cfg ∈ reps,
      interface_distortion
        Node cfg g junc = d)

-- ==================================================
-- MINIMUM EXISTENCE
-- ==================================================

theorem minimal_config_exists
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (hne  : 0 < config_count Node cs) :
    ∃ cfg ∈ cs,
      is_minimal_config Node cs cfg g junc := by

  have hlen : cs ≠ [] := by
    intro h
    simp [config_count, h] at hne

  have hfin : Nonempty (Fin cs.length) := by
    exact ⟨⟨0, by
      simpa [config_count] using hne⟩⟩

  obtain ⟨i_min, h_min⟩ :=
    Finite.exists_min
      (fun i =>
        interface_distortion Node
          (cs.get i)
          g
          junc)

  refine ⟨
    cs.get i_min,
    List.get_mem cs i_min.val i_min.isLt,
    ?_
  ⟩

  constructor

  · exact List.get_mem cs i_min.val i_min.isLt

  · intro cfg' hcfg'

    obtain ⟨i', hi'_lt, hi'_get⟩ :=
      List.mem_iff_get.mp hcfg'

    let fi' : Fin cs.length :=
      ⟨i', hi'_lt⟩

    calc
      interface_distortion Node
        (cs.get i_min) g junc

      ≤ interface_distortion Node
          (cs.get fi') g junc := by
            exact h_min fi'

      _ = interface_distortion Node
            cfg' g junc := by
              congr 1
              exact hi'_get

-- ==================================================
-- REPRESENTATIVE COLLAPSE
-- ==================================================

/-!
If only K observable distortion values exist,
optimization only requires at most K representatives.

This is the first formal collapse theorem.
-/

theorem representative_collapse_sketch
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (K    : ℕ)
    (hK :
      observable_complexity
        Node cs g junc ≤ K) :
    ∃ reps : ConfigSpace Node,

      reps.length ≤ K ∧

      representative_subspace
        Node reps cs g junc := by

  /-
  Sketch:

    For each distinct distortion value d,
    choose one representative cfg realizing d.

    Since there are at most K distinct values,
    there are at most K representatives.
  -/

  sorry

-- ==================================================
-- ENTROPY BOUND SKETCH
-- ==================================================

/-!
Core structural principle:

  Probes cannot invent fundamentally new observable
  asymmetry distinctions beyond those already present
  in the hidden latency field.

Therefore observable complexity is bounded by a
combinatorial function of:

  * signal entropy
  * junction size

The exact bound depends on how many finite sums of
asymmetry classes may occur in interface_distortion.
-/

def distortion_combination_bound
    (entropy : ℕ)
    (junction_size : ℕ) : ℕ :=

  entropy ^ (junction_size * junction_size)

theorem observable_complexity_bounded_by_entropy_sketch
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) :

    observable_complexity Node cs g junc ≤
      distortion_combination_bound
        (signal_entropy Node g junc)
        junc.nodes.card := by

  /-
  Sketch only.

  Proof intuition:

    interface_distortion is built from finite sums
    of asymmetry values.

    The asymmetry vocabulary has size:

      signal_entropy g junc

    Therefore the number of distinct possible
    distortion outputs is bounded by the number
    of finite combinations of those asymmetry
    values across junction interactions.
  -/

  sorry

-- ==================================================
-- FINAL COLLAPSE DIRECTION
-- ==================================================

/-!
Future direction:

  Repetitive / self-similar communication tasks induce
  low signal entropy.

  Low signal entropy forces low observable complexity.

  Low observable complexity forces representative
  collapse.

Therefore:

  stable repetitive communication geometrically
  compresses the effective optimization space.

This is a graph-geometric / causal analogue of
dimensional collapse.
-/

end InterfaceConfig
```
