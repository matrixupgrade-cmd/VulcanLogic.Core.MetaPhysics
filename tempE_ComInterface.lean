import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

namespace InterfaceConfig

-- ==================================================
-- BASIC STRUCTURE (UNCHANGED CORE)
-- ==================================================

variable (Node : Type) [DecidableEq Node]

structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

def applyProbe
    (p : Probe Node)
    (g : Node → Node → ℝ) :
    Node → Node → ℝ :=
  p.transform g

def commutator (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  g i j - g j i

def asymmetry (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  Real.abs (commutator g i j)

def node_asymmetry
    (g : Node → Node → ℝ)
    (nodes : Finset Node)
    (n : Node) : ℝ :=
  ∑ m in nodes, asymmetry g n m

structure Junction where
  nodes : Finset Node

abbrev InterfaceConfig := Probe Node
abbrev ConfigSpace := List (InterfaceConfig Node)

def interface_distortion
    (cfg : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℝ :=
  ∑ n in junc.nodes,
    node_asymmetry Node
      (applyProbe Node cfg g)
      junc.nodes
      n

-- ==================================================
-- OBSERVATIONAL GEOMETRY
-- ==================================================

def observable_complexity
    (cs : ConfigSpace Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  (cs.map (fun cfg => interface_distortion Node cfg g junc)).toFinset.card

-- ==================================================
-- SIGNAL + BASINS
-- ==================================================

/-
A Signal is an input to the communication channel between A and B.
Signals propagate through the graph, and asymmetry causes distortion.

The key insight: signals that follow the *same path* through the
optimization landscape form a basin. Inside a basin, the effective
complexity collapses—only the basin-local entropy matters.
-/
abbrev Signal := Unit  -- can be refined; Unit keeps things concrete

structure Basin where
  signals : Finset Signal

def basin_entropy (b : Basin) : ℕ :=
  b.signals.card

-- ==================================================
-- THE MISSING LINK: signal_to_cfg
-- ==================================================

/-
This is what was absent in the original code.

signal_to_cfg maps each signal to the InterfaceConfig it induces.
Without this, Basin and ConfigSpace are completely unrelated,
and no bound can connect them.

In the A↔B picture: a signal arrives, gets routed through the
interface, and induces a particular probe transformation. Two
signals that induce the same probe are in the same "regime" and
belong to the same basin.
-/
variable (signal_to_cfg : Signal → InterfaceConfig Node)

-- ==================================================
-- BASIN-RESTRICTED CONFIG SPACE
-- ==================================================

/-
The configs that actually matter inside basin b are exactly those
induced by the signals in b. This replaces the "global cs" with
a basin-local one.
-/
def configsInBasin (b : Basin) : ConfigSpace Node :=
  (b.signals.image signal_to_cfg).toList

-- Key properties
lemma configsInBasin_length_le_entropy (b : Basin) :
    (configsInBasin Node signal_to_cfg b).length ≤ basin_entropy b := by
  unfold configsInBasin basin_entropy
  calc (Finset.image signal_to_cfg b.signals).toList.length
      = (Finset.image signal_to_cfg b.signals).card := by
            rw [Finset.toList_length]
    _ ≤ b.signals.card := Finset.card_image_le

-- ==================================================
-- BASIN-LOCAL COMPLEXITY (NOW PROPERLY DEFINED)
-- ==================================================

/-
Critical fix: basin_local_complexity now uses configsInBasin,
so b actually constrains the computation.
-/
def basin_local_complexity
    (b : Basin)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  observable_complexity Node (configsInBasin Node signal_to_cfg b) g junc

-- ==================================================
-- AUXILIARY: observable_complexity ≤ list length
-- ==================================================

lemma observable_complexity_le_length
    (cs : ConfigSpace Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) :
    observable_complexity Node cs g junc ≤ cs.length := by
  unfold observable_complexity
  calc (cs.map (fun cfg => interface_distortion Node cfg g junc)).toFinset.card
      ≤ (cs.map (fun cfg => interface_distortion Node cfg g junc)).length :=
            List.toFinset_card_le _
    _ = cs.length := List.length_map _ _

-- ==================================================
-- THEOREM 1: REPRESENTATIVE COLLAPSE PER BASIN
-- ==================================================

/-
Interpretation: For each basin, there exists a compressed
representative family whose size is bounded by:
  - the basin's own entropy (number of signals in that basin)
  - the number of configs realized inside the basin

This is your "each basin has its own compression" claim.
Signals that take the same path share one representative.
-/
theorem representative_collapse_per_basin
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin) :
    ∃ reps : ConfigSpace Node,
      reps.length ≤ basin_entropy b ∧
      reps.length ≤ (configsInBasin Node signal_to_cfg b).length := by
  -- Take the first (basin_entropy b) elements of configsInBasin b.
  -- This is the "compressed" representative family.
  let cs := configsInBasin Node signal_to_cfg b
  let n  := Nat.min (basin_entropy b) cs.length
  refine ⟨cs.take n, ?_, ?_⟩
  · -- reps.length ≤ basin_entropy b
    have h1 : (cs.take n).length = Nat.min n cs.length :=
      List.length_take n cs
    rw [h1]
    exact Nat.le_trans (Nat.min_le_left n cs.length) (Nat.min_le_left _ _)
  · -- reps.length ≤ (configsInBasin b).length
    have h1 : (cs.take n).length = Nat.min n cs.length :=
      List.length_take n cs
    rw [h1]
    exact Nat.min_le_right n cs.length

-- ==================================================
-- THEOREM 2: COMPLEXITY BOUNDED PER BASIN
-- ==================================================

/-
Interpretation: The observable complexity inside a basin is
bounded by basin_entropy b (the number of signals in that basin).

This is your core compression claim:
  "A signal in a stable high-entropy optimum, once placed in a
   basin, has a much simplified version that acts like the global
   optimum for all signals whose paths are highly similar."

The bound is basin_entropy b (not the full distortion_combination_bound)
because at this layer we are simply counting how many distinct configs
the basin's signals can induce—which is at most b.signals.card.

A tighter combinatorial bound (the exponential one) requires
an additional hypothesis about how many distinct distortion values
each (i,j) pair can take inside the basin; that is left as an
axiom below that you can later refine with real measure theory.
-/
theorem observable_complexity_bounded_per_basin
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin) :
    basin_local_complexity Node signal_to_cfg b g junc ≤ basin_entropy b := by
  unfold basin_local_complexity
  calc observable_complexity Node (configsInBasin Node signal_to_cfg b) g junc
      ≤ (configsInBasin Node signal_to_cfg b).length :=
            observable_complexity_le_length Node _ g junc
    _ ≤ basin_entropy b :=
            configsInBasin_length_le_entropy Node signal_to_cfg b

-- ==================================================
-- TIGHTER EXPONENTIAL BOUND (REQUIRES EXTRA HYPOTHESIS)
-- ==================================================

/-
Your original distortion_combination_bound was:
  entropy ^ (junction_size * junction_size)

This comes from the argument:
  - The junction has k nodes, so k*k ordered pairs (i,j).
  - Inside the basin, each pair has at most `entropy` distinct
    effective distortion values.
  - So the number of distinct global distortion patterns is
    at most entropy^(k*k).

To encode this cleanly, we need a hypothesis about the
per-pair distortion count. This is the one piece that truly
depends on the structure of your channel model.
-/

def distortion_combination_bound (entropy : ℕ) (junction_size : ℕ) : ℕ :=
  entropy ^ (junction_size * junction_size)

/-
The hypothesis: inside basin b, the number of distinct distortion
values each ordered pair (i,j) can take is bounded by basin_entropy b.

In the A↔B picture: signals in the same basin compress the per-link
variability down to at most (number of signals in basin) distinct values.
-/
axiom basin_per_pair_distortion_bound
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin) :
    (configsInBasin Node signal_to_cfg b).map
      (fun cfg => interface_distortion Node cfg g junc)
      |>.toFinset.card
    ≤ basin_entropy b ^ (junc.nodes.card * junc.nodes.card)

/-
With that axiom in hand, the exponential bound is immediate:
observable_complexity is exactly the LHS of the axiom.
-/
theorem observable_complexity_bounded_exponential
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin) :
    basin_local_complexity Node signal_to_cfg b g junc ≤
      distortion_combination_bound (basin_entropy b) junc.nodes.card := by
  unfold basin_local_complexity observable_complexity distortion_combination_bound
  exact basin_per_pair_distortion_bound Node signal_to_cfg g junc b

-- ==================================================
-- FINAL PICTURE (COMMENTS)
-- ==================================================

/-
WHAT THIS FILE NOW ENCODES:

1. A and B communicate through an asymmetric graph channel.
   Distortion arises from asymmetry: g(i,j) ≠ g(j,i).

2. Signals induce configurations (probes) via signal_to_cfg.

3. Signals that induce the same probe, or probes with the same
   distortion pattern at the junction, belong to the same basin.

4. Inside each basin:
   - The effective config space is configsInBasin (at most b.signals.card configs).
   - The observable complexity is bounded by basin_entropy b.
   - (With extra hypothesis) it is bounded by the tighter exponential.

5. Global behavior = union of local basin collapses.
   You never need global simplicity.
   You only need local structural stability inside finite partitions.

WHAT STILL NEEDS WORK:

- basin_per_pair_distortion_bound is an axiom.
  To make it a theorem, you need to encode *why* each (i,j) pair
  has at most entropy distinct values—this comes from the channel
  model (e.g. signal quantization, finite alphabet, Lipschitz bounds
  on probe transforms).

- Signal = Unit is a placeholder.
  Once you refine Signal to carry real content (e.g. a bit string,
  a finite alphabet value), signal_to_cfg becomes a concrete map
  and basin membership becomes decidable.

- The "rotation" intuition (A and B rotating to minimize loss)
  would be encoded as: for each basin, the optimal probe is the
  argmin of basin_local_complexity over all probes.
  That is a separate existence theorem, provable once you have
  compactness of the probe space or a finite discretization.
-/

end InterfaceConfig
