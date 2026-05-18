import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

/-! ====================================================
  INTERFACE CONFIGURATION
  ────────────────────────────────────────────────────
  Core intuition:
    Entity A and entity B each have a hidden internal
    graph.  They connect at a junction — a boundary
    where signals pass between them.

    An *interface configuration* is a Probe applied at
    that junction: it determines how A's signal enters B's
    latency field (and vice versa).

    Different configurations produce different amounts of
    signal distortion, measured as asymmetry at the
    boundary (commutator magnitude).

    The key claim:
      If A and B are sufficiently complex — meaning the
      space of possible interface configurations is large
      enough — then at least one configuration exists
      that achieves the minimum observable distortion.

    We do not construct that configuration.
    We do not identify it.
    We prove it exists, by a counting argument over the
    configuration space.

  RELATIONSHIP TO CausalGraph:
    Probe, applyProbe, asymmetry, node_asymmetry,
    structural_diversity are all reused directly from
    CausalGraph.  This file adds only the layer that
    reasons about *families* of probes as a configuration
    space, and what complexity of that space guarantees.

  LAYERS
  1. Interface vocabulary    — junction, configuration space
  2. Distortion measure      — per-configuration asymmetry
  3. Configuration ordering  — which interface is "better"
  4. Existence theorem       — minimum distortion exists
                               given sufficient complexity
==================================================== -/

namespace InterfaceConfig

-- ────────────────────────────────────────────────────
-- Reuse CausalGraph primitives inline
-- (If importing CausalGraph, replace these with opens)
-- ────────────────────────────────────────────────────

variable (Node : Type) [DecidableEq Node]

structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

def applyProbe
    (p : Probe Node)
    (g : Node → Node → ℝ) : Node → Node → ℝ :=
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

-- ────────────────────────────────────────────────────
-- LAYER 1: INTERFACE VOCABULARY
-- ────────────────────────────────────────────────────

/-!
  A Junction is the boundary between A and B:
  the set of nodes where their signals meet.

  An InterfaceConfig is a Probe applied at that junction.
  It encodes *how* A and B are hooked up —
  which of A's signals feed into which of B's latency
  paths, and with what transformation.

  A ConfigSpace is the full list of ways A and B
  *could* hook up.  Its length is the combinatorial
  count of available configurations.
-/

/-- The boundary nodes where A and B meet. -/
structure Junction where
  nodes : Finset Node

/-- One particular way A and B are hooked up. -/
abbrev InterfaceConfig := Probe Node

/-- The full space of possible hookups between A and B. -/
abbrev ConfigSpace := List (InterfaceConfig Node)

/-- The number of available interface configurations.
    This is the "complexity" of the A-B connection. -/
def config_count (cs : ConfigSpace Node) : ℕ :=
  cs.length


-- ────────────────────────────────────────────────────
-- LAYER 2: DISTORTION MEASURE
-- ────────────────────────────────────────────────────

/-!
  The distortion of a configuration is the total
  asymmetry it produces at the junction boundary,
  given the underlying hidden latency field g.

  This is the signal deflection caused by the mismatch
  between how A and B are hooked up and the hidden
  structure of their internal graphs.

  Lower distortion = better interface fit.
  Zero distortion  = perfect structural alignment
                     (symmetric interface).
-/

/-- Distortion of one interface configuration at the junction. -/
def interface_distortion
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℝ :=
  ∑ n in junc.nodes,
    node_asymmetry Node (applyProbe Node cfg g) junc.nodes n

/-- Distortion is nonneg — can't have negative signal loss. -/
theorem interface_distortion_nonneg
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) :
    0 ≤ interface_distortion Node cfg g junc := by
  unfold interface_distortion node_asymmetry asymmetry
  apply Finset.sum_nonneg; intro n _
  apply Finset.sum_nonneg; intro m _
  exact Real.abs_nonneg _

/-- The distortion value of each configuration in the space,
    as a function Fin(count) → ℝ. -/
def distortion_map
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) :
    Fin cs.length → ℝ :=
  fun i => interface_distortion Node (cs.get i) g junc


-- ────────────────────────────────────────────────────
-- LAYER 3: CONFIGURATION ORDERING
-- ────────────────────────────────────────────────────

/-!
  One configuration is "better than or equal to" another
  if it produces no more distortion.

  A configuration is *minimal* in the space if no other
  configuration produces strictly less distortion.

  We do not require a unique minimum — only that some
  configuration achieves the minimum value.
-/

/-- cfg₁ is at least as good as cfg₂ at junction junc. -/
def cfg_leq
    (cfg₁ cfg₂ : InterfaceConfig Node)
    (g          : Node → Node → ℝ)
    (junc       : Junction Node) : Prop :=
  interface_distortion Node cfg₁ g junc ≤
  interface_distortion Node cfg₂ g junc

/-- A configuration is minimal in cs if no member of cs
    has strictly lower distortion. -/
def is_minimal_config
    (cs   : ConfigSpace Node)
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : Prop :=
  cfg ∈ cs ∧
  ∀ cfg' ∈ cs,
    interface_distortion Node cfg g junc ≤
    interface_distortion Node cfg' g junc


-- ────────────────────────────────────────────────────
-- LAYER 4: EXISTENCE THEOREM
-- ────────────────────────────────────────────────────

/-!
  CORE CLAIM:
    If the configuration space is nonempty
    (i.e. config_count > 0, meaning A and B have at least
    one way to hook up), then a minimal configuration exists.

  This is a finite minimum existence theorem.
  The configuration space is a finite list; the distortion
  map is a function Fin(n) → ℝ on a nonempty finite type;
  therefore a minimum is achieved.

  The "complexity" condition (config_count cs > 0) is
  exactly the requirement that the space is nonempty.
  Richer internal graphs give larger config spaces, which
  gives more room for a low-distortion hookup to exist —
  but the existence of *some* minimum holds as soon as
  the space is nonempty at all.

  The interesting later theorem (not proven here) would be:
    As config_count grows, the minimum distortion achievable
    decreases (or at least does not increase).
  That requires a monotonicity argument over families of
  configuration spaces, which is a natural next layer.
-/

/-- A nonempty config space always has a minimum-distortion
    configuration.  Existence, not construction. -/
theorem minimal_config_exists
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (hne  : 0 < config_count Node cs) :
    ∃ cfg ∈ cs, is_minimal_config Node cs cfg g junc := by
  -- cs is nonempty
  have hlen : cs ≠ [] := by
    intro h; simp [config_count, h] at hne
  -- Get the index of the minimum over Fin(cs.length)
  have hfin : Nonempty (Fin cs.length) := by
    exact ⟨⟨0, by simp [config_count] at hne; exact hne⟩⟩
  -- The distortion map achieves a minimum on a nonempty Fintype
  obtain ⟨i_min, h_min⟩ :=
    Finite.exists_min (distortion_map Node cs g junc)
  -- The minimizing config is cs.get i_min
  refine ⟨cs.get i_min, List.get_mem cs i_min.val i_min.isLt, ?_⟩
  constructor
  · exact List.get_mem cs i_min.val i_min.isLt
  · intro cfg' hcfg'
    -- Find the index of cfg' in cs
    obtain ⟨i', hi'_lt, hi'_get⟩ := List.mem_iff_get.mp hcfg'
    have hi'fin : Fin cs.length := ⟨i', hi'_lt⟩
    calc interface_distortion Node (cs.get i_min) g junc
        = distortion_map Node cs g junc i_min := rfl
      _ ≤ distortion_map Node cs g junc hi'fin := h_min hi'fin
      _ = interface_distortion Node (cs.get hi'fin) g junc := rfl
      _ = interface_distortion Node cfg' g junc := by
            congr 1; exact hi'_get

/-!
  MONOTONICITY SKETCH (for later):

  If cs₁ ⊆ cs₂ as configuration spaces (cs₁ is a sublist
  of cs₂), then:

    min_{cfg ∈ cs₂} distortion(cfg) ≤
    min_{cfg ∈ cs₁} distortion(cfg)

  Because cs₂ has at least as many options to choose from.
  This is where "more complex A and B → lower minimum
  distortion" would be stated precisely.

  def min_distortion (cs g junc hne) : ℝ :=
    the distortion at the minimizer from minimal_config_exists

  theorem larger_space_lower_min
      (cs₁ cs₂ : ConfigSpace Node)
      (hsub : ∀ cfg ∈ cs₁, cfg ∈ cs₂)
      ... :
      min_distortion cs₂ ≤ min_distortion cs₁
-/

end InterfaceConfig
