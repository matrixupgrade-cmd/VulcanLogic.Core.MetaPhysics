import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

namespace CausalGraph

variable (Node : Type) [DecidableEq Node]

/-! ===============================
  LAYERED ARCHITECTURE
  1. Calibration
  2. Residuals
  3. Signatures
  4. Probing
  5. Symmetry Algebra + Semi-Group
  6. Inference
  =============================== -/

-- LAYER 1: CALIBRATION
structure VerifiedNormalRange where
  verified_min : ℕ
  verified_max : ℕ
  valid : verified_min ≤ verified_max

structure Calibration where
  baseline_nodes : Finset Node
  normal_range   : VerifiedNormalRange

-- LAYER 2: RESIDUALS
structure SingleObservation where
  node       : Node
  iterations : ℕ

def outside_verified_range
    (obs  : SingleObservation)
    (norm : VerifiedNormalRange) : Prop :=
  obs.iterations < norm.verified_min ∨
  obs.iterations > norm.verified_max

def distinct_from_verified
    (obs  : SingleObservation)
    (norm : VerifiedNormalRange) : Prop :=
  outside_verified_range obs norm

-- LAYER 3: SIGNATURES
structure Observation where
  obs_node : Node
  residual : Node → ℝ

def stable_signature (C : Calibration) (Obs : Observation) : Prop :=
  ∃ n ∈ C.baseline_nodes, Obs.obs_node ≠ n ∧ Obs.residual n ≠ 0

def anomalous_interface
    (C : Calibration)
    (Obs : Observation) : Prop :=
  ∀ n ∈ C.baseline_nodes, n ≠ Obs.obs_node → Obs.residual n ≠ 0

-- LAYER 4: PROBING
structure ReturnGeometry where
  node_set       : Finset Node
  expected_delay : Node → Node → ℝ
  valid          : ∀ i j, 0 < expected_delay i j

structure ProbeSequence where
  iterations : ℕ → Node → Node → ℝ

def probe_residual
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (t        : ℕ)
    (i j      : Node) : ℝ :=
  probe.iterations t i j - baseline.expected_delay i j

-- Temporal commutator across two ping times
def temporal_commutator
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (t0 t1    : ℕ)
    (i j      : Node) : ℝ :=
  (probe_residual baseline probe t0 i j - probe_residual baseline probe t0 j i) -
  (probe_residual baseline probe t1 i j - probe_residual baseline probe t1 j i)

def structural_diversity
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (nodes    : Finset Node) : ℝ :=
  ∑ n in nodes, ∑ m in nodes,
    if n ≠ m then Real.abs (temporal_commutator baseline probe 0 1 n m)
    else 0

def detectable_threshold : ℝ := 1.0

def is_latency_node
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (n        : Node)
    (nodes    : Finset Node)
    (ϵ        : ℝ) : Prop :=
  ∃ m ∈ nodes, n ≠ m ∧ Real.abs (temporal_commutator baseline probe 0 1 n m) > ϵ

theorem structural_diversity_guarantees_latency
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (nodes    : Finset Node)
    (ϵ        : ℝ)
    (h        : structural_diversity baseline probe nodes > ϵ) :
    ∃ n ∈ nodes, is_latency_node baseline probe n nodes ϵ := by
  unfold structural_diversity is_latency_node temporal_commutator
  have exists_term : ∃ n ∈ nodes, ∃ m ∈ nodes, n ≠ m ∧
      Real.abs ((probe_residual baseline probe 0 n m - probe_residual baseline probe 0 m n) -
                (probe_residual baseline probe 1 n m - probe_residual baseline probe 1 m n)) > 0 := by
    contrapose! h
    intros H
    apply Finset.sum_nonneg
    intros n hn
    apply Finset.sum_nonneg
    intros m hm
    split_ifs
    · linarith
    · exact le_rfl
  rcases exists_term with ⟨n, hn, m, hm, hnm, hval⟩
  use n, hn
  use m, hm, hnm, hval

-- LAYER 5: SYMMETRY ALGEBRA + SEMI-GROUP
def latency_commutator
    (latency : Node → Node → ℝ)
    (i j     : Node) : ℝ :=
  latency i j - latency j i

def symmetric_pair
    (latency : Node → Node → ℝ)
    (i j     : Node) : Prop :=
  latency_commutator latency i j = 0

def symmetric_region
    (latency : Node → Node → ℝ)
    (nodes   : Finset Node) : Prop :=
  ∀ i ∈ nodes, ∀ j ∈ nodes, symmetric_pair latency i j

def asymmetric_interface
    (latency : Node → Node → ℝ)
    (i j     : Node) : Prop :=
  latency_commutator latency i j ≠ 0

theorem commutator_antisymmetry
    (latency : Node → Node → ℝ)
    (i j     : Node) :
    latency_commutator latency i j = -(latency_commutator latency j i) := by
  unfold latency_commutator
  ring

theorem symmetric_pair_comm
    (latency : Node → Node → ℝ)
    (i j     : Node)
    (h       : symmetric_pair latency i j) :
    symmetric_pair latency j i := by
  unfold symmetric_pair latency_commutator at *
  linarith

structure PathMonoid where
  carrier : Node → Node → ℝ
  op      : ℝ → ℝ → ℝ := λ x y => x + y
  id      : ℝ := 0
  assoc   : ∀ x y z, op (op x y) z = op x (op y z) := by intros; rfl
  left_id : ∀ x, op id x = x := by intros; rfl
  right_id: ∀ x, op x id = x := by intros; rfl
  comm    : Prop := ∀ i j, latency_commutator carrier i j = 0

def commutator_witness
    (probe : ProbeSequence)
    (t     : ℕ)
    (n     : Node)
    (nodes : Finset Node) : Prop :=
  ∃ m ∈ nodes, n ≠ m ∧ asymmetric_interface (probe.iterations t) n m

theorem latency_node_is_commutator_witness
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (n        : Node)
    (nodes    : Finset Node)
    (ϵ        : ℝ)
    (hn_nodes : n ∈ nodes)
    (h_sym    : symmetric_region (baseline.expected_delay) nodes)
    (h_lat    : is_latency_node baseline probe n nodes ϵ) :
    commutator_witness probe 0 n nodes := by
  rcases h_lat with ⟨m, hm, hnm, hval⟩
  use m, hm, hnm
  unfold asymmetric_interface temporal_commutator probe_residual
  -- Since baseline is symmetric, residual difference = temporal_commutator
  -- By definition of is_latency_node, abs(temporal_commutator) > ϵ ≠ 0
  intro h_zero
  linarith

-- LAYER 6: UNIFIED INFERENCE
def informative_node
    (C : Calibration)
    (Obs : Observation)
    (baseline : ReturnGeometry)
    (probe : ProbeSequence)
    (n : Node)
    (ϵ : ℝ) : Prop :=
  stable_signature C Obs ∧ Obs.obs_node = n ∨
  is_latency_node baseline probe n C.baseline_nodes ϵ

theorem informative_nodes_exist
    (C : Calibration)
    (Obs : Observation)
    (baseline : ReturnGeometry)
    (probe : ProbeSequence)
    (ϵ : ℝ)
    (h
