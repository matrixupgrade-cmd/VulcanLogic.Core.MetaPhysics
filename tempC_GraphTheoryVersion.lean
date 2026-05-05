import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset Classical

/-!
# Observer-Limited Causal Detectability (Weighted Flow Core)

This formalization models:

- A causal system as a weighted directed graph
- A trajectory as a finite path through the graph
- An observer as a set of visible "first-layer nodes"
- Probability as normalized causal flow into observer interface

Future extension target:
- information loss as divergence between flows
-/


/-!
## Basic Setup
-/

variable (Node : Type) [Fintype Node] [DecidableEq Node]

/--
Weighted causal graph.
Each edge encodes strength / transition likelihood.
-/
structure Graph (Node : Type) where
  weight : Node → Node → ℚ


/--
Finite causal path through the system.
-/
abbrev Path (Node : Type) := List Node


/-!
## Observer = first-layer interface
-/

structure Observer (Node : Type) where
  obs : Finset Node


/-!
## Path validity (causal consistency)
A path is valid if all transitions have positive weight.
-/

def valid_path
    (G : Graph Node) : Path Node → Prop
  | [] => False
  | [x] => True
  | x :: y :: rest =>
      G.weight x y > 0 ∧ valid_path G (y :: rest)


/-!
## Path weight (causal flow strength)
Multiplicative accumulation of edge weights.
-/

def path_weight
    (G : Graph Node) : Path Node → ℚ
  | [] => 0
  | [x] => 1
  | x :: y :: rest =>
      G.weight x y * path_weight G (y :: rest)


/-!
## Observer termination condition
A path is observable if it ends in the observer interface.
-/

def terminates_in_observer
    (O : Observer Node) : Path Node → Prop :=
  fun p =>
    match p.reverse with
    | [] => False
    | last :: _ => last ∈ O.obs


/-
## Observable flow (numerator)
Total causal flow reaching observer interface.
-/
def observable_flow
    (G : Graph Node)
    (O : Observer Node) : ℚ :=
  ∑ p in (Finset.univ : Finset (Path Node)),
    if valid_path Node G p ∧ terminates_in_observer Node O p
    then path_weight Node G p
    else 0


/-
## Total causal flow (denominator)
All flow in the system.
-/
def total_flow
    (G : Graph Node) : ℚ :=
  ∑ p in (Finset.univ : Finset (Path Node)),
    if valid_path Node G p
    then path_weight Node G p
    else 0


/-
## Probability = fraction of causal flow reaching observer interface
Core identity of the model.
-/
def path_probability
    (G : Graph Node)
    (O : Observer Node) : ℚ :=
  observable_flow Node G O / total_flow Node G
