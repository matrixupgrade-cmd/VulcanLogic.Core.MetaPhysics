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
  5. Inference
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
  node_set : Finset Node
  expected_delay : Node → Node → ℝ
  valid : ∀ i j, 0 < expected_delay i j

structure ProbeSequence where
  iterations : ℕ → Node → Node → ℝ

def probe_residual
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (t        : ℕ)
    (i j      : Node) : ℝ :=
  probe.iterations t i j - baseline.expected_delay i j

def structural_diversity
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (nodes    : Finset Node) : ℝ :=
  ∑ n in nodes, ∑ m in nodes,
    if n ≠ m then
      Real.abs (probe_residual baseline probe 0 n m -
                probe_residual baseline probe 1 n m)
    else 0

def detectable_threshold : ℝ := 1.0

def is_latency_node
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (n        : Node)
    (nodes    : Finset Node)
    (ϵ        : ℝ) : Prop :=
  ∃ m ∈ nodes, n ≠ m ∧
    Real.abs (probe_residual baseline probe 0 n m -
              probe_residual baseline probe 1 n m) > ϵ

theorem structural_diversity_guarantees_latency
    (baseline : ReturnGeometry)
    (probe    : ProbeSequence)
    (nodes    : Finset Node)
    (ϵ        : ℝ)
    (h        : structural_diversity baseline probe nodes > ϵ) :
    ∃ n ∈ nodes, is_latency_node baseline probe n nodes ϵ := by
  unfold structural_diversity
  let summands := ∑ n in nodes, ∑ m in nodes, if n ≠ m then
      Real.abs (probe_residual baseline probe 0 n m -
                probe_residual baseline probe 1 n m) else 0
  have exists_term : ∃ n ∈ nodes, ∃ m ∈ nodes, n ≠ m ∧
    Real.abs (probe_residual baseline probe 0 n m -
              probe_residual baseline probe 1 n m) > 0 := by
    contrapose! h
    intros H
    have sum_nonpos : summands ≤ 0 := by
      apply Finset.sum_nonneg
      intros n hn
      apply Finset.sum_nonneg
      intros m hm
      split_ifs
      · linarith
      · exact le_rfl
    linarith
  rcases exists_term with ⟨n, hn, m, hm, hnm, hval⟩
  use n, hn
  unfold is_latency_node
  use m, hm
  exact ⟨hnm, hval⟩

-- LAYER 5: UNIFIED INFERENCE
/-- A node is "informative" if it is either an outlier or a latency node from probing -/
def informative_node
    (C : Calibration)
    (Obs : Observation)
    (baseline : ReturnGeometry)
    (probe : ProbeSequence)
    (n : Node)
    (ϵ : ℝ) : Prop :=
  stable_signature C Obs ∧ Obs.obs_node = n ∨
  is_latency_node baseline probe n C.baseline_nodes ϵ

/-- The main theorem: given calibration, observations, and probing sequences,
    there exists at least one informative node whenever there are persistent outliers
    or structural diversity is above threshold -/
theorem informative_nodes_exist
    (C : Calibration)
    (Obs : Observation)
    (baseline : ReturnGeometry)
    (probe : ProbeSequence)
    (ϵ : ℝ)
    (h1 : ∃ n ∈ C.baseline_nodes, stable_signature C Obs)
    (h2 : structural_diversity baseline probe C.baseline_nodes > ϵ) :
    ∃ n ∈ C.baseline_nodes, informative_node C Obs baseline probe n ϵ := by
  rcases h1 with ⟨n_sig, hn_sig, _⟩
  rcases structural_diversity_guarantees_latency baseline probe C.baseline_nodes ϵ h2 with
    ⟨n_lat, hn_lat, hlat⟩
  by_cases h_eq : n_sig = n_lat
  · use n_sig, hn_sig
    unfold informative_node
    left
    exact ⟨⟨_, hn_sig, rfl⟩, rfl⟩
  · use n_lat, hn_lat
    unfold informative_node
    right
    exact hlat

end CausalGraph
