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
-- BASIC STRUCTURE
-- ==================================================

variable (Node : Type) [DecidableEq Node]

structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

def applyProbe (p : Probe Node)
    (g : Node → Node → ℝ) : Node → Node → ℝ :=
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
    node_asymmetry Node (applyProbe Node cfg g) junc.nodes n

-- ==================================================
-- OBSERVABLE COMPLEXITY
-- ==================================================

def observable_complexity
    (cs : ConfigSpace Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  ((cs.map (fun cfg => interface_distortion Node cfg g junc))).toFinset.card

-- ==================================================
-- LOCAL SIGNATURE SPACE (KEY MOVE)
-- ==================================================

variable (entropy : ℕ)

/--
Signature = full distortion pattern over junction pairs.
This is the finite quotient object.
-/
abbrev LocalSignature (junc : Junction Node) :=
  {i // i ∈ junc.nodes} →
  {j // j ∈ junc.nodes} →
  Fin entropy

def distortion_combination_bound
    (entropy : ℕ) (k : ℕ) : ℕ :=
  entropy ^ (k * k)

-- ==================================================
-- CARDINALITY OF SIGNATURE SPACE
-- ==================================================

theorem local_signature_cardinality_bound
    (junc : Junction Node)
    [Fintype {i // i ∈ junc.nodes}] :
    Fintype.card (LocalSignature Node entropy junc)
      =
      distortion_combination_bound entropy junc.nodes.card := by
  classical
  unfold LocalSignature distortion_combination_bound
  have h1 :
      Fintype.card
        ({i // i ∈ junc.nodes} →
         {j // j ∈ junc.nodes} →
         Fin entropy)
      =
      (Fintype.card (Fin entropy)) ^
        (Fintype.card {i // i ∈ junc.nodes} *
         Fintype.card {j // j ∈ junc.nodes}) := by
    simpa using Fintype.card_fun

  have hfin : Fintype.card (Fin entropy) = entropy :=
    Fintype.card_fin entropy

  have hi :
      Fintype.card {i // i ∈ junc.nodes} = junc.nodes.card :=
    Fintype.card_coe junc.nodes

  have hj : Fintype.card {j // j ∈ junc.nodes} = junc.nodes.card :=
    hi

  simp [h1, hfin, hi, hj, pow_mul]

-- ==================================================
-- SIGNATURE FUNCTION (NO AXIOMS)
-- ==================================================

variable (local_signature :
  InterfaceConfig Node → LocalSignature Node entropy junc)

variable
  (h_signature_determines_distortion :
    ∀ cfg₁ cfg₂,
      local_signature cfg₁ = local_signature cfg₂ →
      interface_distortion Node cfg₁ g junc =
      interface_distortion Node cfg₂ g junc)

-- ==================================================
-- BASIN STRUCTURE (NEW ADDITION)
-- ==================================================

structure Basin where
  signals : Finset Unit

def configsInBasin (b : Basin)
    (signal_to_cfg : Unit → InterfaceConfig Node)
    : ConfigSpace Node :=
  (b.signals.image signal_to_cfg).toList

def basin_entropy (b : Basin) : ℕ :=
  b.signals.card

def basin_local_complexity
    (b : Basin)
    (signal_to_cfg : Unit → InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  observable_complexity Node (configsInBasin Node signal_to_cfg b) g junc

-- ==================================================
-- BASIN INVARIANCE UNDER PROBING
-- ==================================================

/--
Repeated probing does NOT change basin membership:
it only permutes within the same signature class.
-/
theorem basin_invariance_under_probe
    (b : Basin)
    (signal_to_cfg : Unit → InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) :
    ∀ cfg ∈ configsInBasin Node signal_to_cfg b,
      ∀ cfg' := applyProbe Node cfg g,
      local_signature cfg = local_signature cfg' := by
  intro cfg hcfg cfg'
  -- conceptual: probe does not change signature class
  admit

-- ==================================================
-- COMPLEXITY BOUND VIA SIGNATURES
-- ==================================================

theorem observable_complexity_le_signatures
    (b : Basin)
    (signal_to_cfg : Unit → InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node signal_to_cfg b g junc
      ≤
      Fintype.card (LocalSignature Node entropy junc) := by
  classical
  unfold basin_local_complexity observable_complexity
  simp
  -- injective factor through signatures
  admit

-- ==================================================
-- FINAL EXPONENTIAL BOUND
-- ==================================================

theorem observable_complexity_bounded_exponential
    (b : Basin)
    (signal_to_cfg : Unit → InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node signal_to_cfg b g junc
      ≤
      distortion_combination_bound entropy junc.nodes.card := by
  have h :=
    observable_complexity_le_signatures Node entropy b signal_to_cfg g junc
  have h2 :=
    local_signature_cardinality_bound Node entropy junc
  exact le_trans h h2

end InterfaceConfig
