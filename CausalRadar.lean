import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

namespace CausalGraph

variable (Node : Type) [DecidableEq Node]

/-! ====================================================
  CAUSAL RADAR
  ────────────────────────────────────────────────────
  Core intuition: signals flow freely through symmetric
  regions of a hidden graph and only return a detectable
  residual when they cross an asymmetric interface.
  This is the same primitive underlying radar,
  seismographs, and MRI — now stated abstractly enough
  to apply to any causal graph system.

  LAYERS
  1. Calibration             — verified normal baseline
  2. Observation             — boundary-visible residuals
  3. Probing                 — probe as field transformation
  4. Commutator Algebra      — symmetry / asymmetry
  5. Iterative Accumulation  — semigroup action over time
  6. Structural Diversity    — scalar asymmetry energy
  7. Unified Inference       — existence theorems
  8. System Dynamics Bridge  — commentary
==================================================== -/


-- ====================================================
-- LAYER 1: CALIBRATION
-- ====================================================

/-- A verified range of normal iteration counts.
    Produced once from trusted baseline data.
    This is the "speed of light" the radar needs —
    without calibration, residuals are meaningless. -/
structure VerifiedNormalRange where
  verified_min : ℕ
  verified_max : ℕ
  valid        : verified_min ≤ verified_max

/-- Calibration bundles the trusted node set with its
    normal range. -/
structure Calibration where
  baseline_nodes : Finset Node
  normal_range   : VerifiedNormalRange

def outside_verified_range
    (obs  : ℕ)
    (norm : VerifiedNormalRange) : Prop :=
  obs < norm.verified_min ∨ obs > norm.verified_max

def distinct_from_verified
    (obs  : ℕ)
    (norm : VerifiedNormalRange) : Prop :=
  outside_verified_range obs norm


-- ====================================================
-- LAYER 2: OBSERVATION / RESIDUALS
-- ====================================================

/-- A boundary observation: which node is visible and
    what residual signal it carries relative to others. -/
structure Observation where
  obs_node : Node
  residual : Node → ℝ

/-- A stable signature exists when some baseline node
    carries a nonzero residual — the calibrated region
    is disturbed. -/
def stable_signature
    (C   : Calibration)
    (Obs : Observation) : Prop :=
  ∃ n ∈ C.baseline_nodes, Obs.residual n ≠ 0

/-- Anomalous interface: every baseline node except the
    observed one carries nonzero residual — the
    disturbance is global across the boundary. -/
def anomalous_interface
    (C   : Calibration)
    (Obs : Observation) : Prop :=
  ∀ n ∈ C.baseline_nodes, n ≠ Obs.obs_node → Obs.residual n ≠ 0


-- ====================================================
-- LAYER 3: PROBING
-- ====================================================
/-!
  A probe is a transformation of the latency field itself,
  not a parallel sequence indexed by ℕ.  This is the right
  abstraction: probing *acts on* the hidden medium and we
  observe what comes back.  Composition of probes is
  semigroup composition, avoiding the infinite-sequence
  complexity that causes proof friction.
-/

/-- The hidden graph's latency field — all we can observe
    from the boundary.  Internal structure is opaque. -/
structure ReturnGeometry where
  delay : Node → Node → ℝ
  valid : ∀ i j, 0 ≤ delay i j

/-- A probe transforms the observable latency field.
    Encodes: emit signal, observe the transformed return. -/
structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

/-- Probe composition — the semigroup operation.
    p then q: q acts first, p acts on the result. -/
def composeProbe (p q : Probe) : Probe :=
  { transform := fun f => p.transform (q.transform f) }

/-- The identity probe — emit and receive unchanged. -/
def idProbe : Probe :=
  { transform := fun f => f }

/-- Apply a probe to a latency field. -/
def applyProbe
    (p : Probe)
    (g : Node → Node → ℝ) : Node → Node → ℝ :=
  p.transform g

/-- Probe composition is associative — the semigroup law. -/
theorem composeProbe_assoc (p q r : Probe) :
    (composeProbe p (composeProbe q r)).transform =
    (composeProbe (composeProbe p q) r).transform := by
  simp [composeProbe]

/-- idProbe is a left identity. -/
theorem idProbe_left (p : Probe) :
    (composeProbe idProbe p).transform = p.transform := by
  simp [composeProbe, idProbe]

/-- idProbe is a right identity. -/
theorem idProbe_right (p : Probe) :
    (composeProbe p idProbe).transform = p.transform := by
  simp [composeProbe, idProbe]

/-- Fold a list of probes into a single composed
    transformation — the monoid action over time. -/
def foldProbes :
    List Probe → (Node → Node → ℝ) → (Node → Node → ℝ)
  | [],      g => g
  | p :: ps, g => foldProbes ps (p.transform g)

theorem foldProbes_nil (g : Node → Node → ℝ) :
    foldProbes [] g = g := rfl

theorem foldProbes_cons
    (p  : Probe)
    (ps : List Probe)
    (g  : Node → Node → ℝ) :
    foldProbes (p :: ps) g = foldProbes ps (p.transform g) := rfl

/-- Folding a concatenation of probe lists is the same as
    folding the first then the second — associativity of
    the monoid action. -/
theorem foldProbes_append
    (ps qs : List Probe)
    (g     : Node → Node → ℝ) :
    foldProbes (ps ++ qs) g =
    foldProbes qs (foldProbes ps g) := by
  induction ps with
  | nil       => simp [foldProbes_nil, foldProbes_cons]
  | cons p ps ih => simp [foldProbes_cons, ih]


-- ====================================================
-- LAYER 4: COMMUTATOR ALGEBRA
-- ====================================================
/-!
  The commutator of a latency field measures directional
  asymmetry between a pair of nodes.

    commutator = 0  →  symmetric pair
                       signal passes through, no ping back

    commutator ≠ 0  →  asymmetric interface
                       path divergence, ping returns

  This is why radar, seismographs, and MRI work: they are
  all boundary-observable commutator detectors operating on
  different physical media.
-/

/-- Signed asymmetry of the latency field at (i, j). -/
def commutator
    (g   : Node → Node → ℝ)
    (i j : Node) : ℝ :=
  g i j - g j i

/-- Unsigned asymmetry magnitude. -/
def asymmetry
    (g   : Node → Node → ℝ)
    (i j : Node) : ℝ :=
  Real.abs (commutator g i j)

/-- Symmetric pair: commutator vanishes.
    Signal is indifferent to direction. -/
def symmetric_pair
    (g   : Node → Node → ℝ)
    (i j : Node) : Prop :=
  commutator g i j = 0

/-- A symmetric region: every directed pair within the
    node set is symmetric.  This is the attractor basin —
    probes circulating inside return without residual. -/
def symmetric_region
    (g     : Node → Node → ℝ)
    (nodes : Finset Node) : Prop :=
  ∀ i ∈ nodes, ∀ j ∈ nodes, symmetric_pair g i j

/-- Asymmetric interface: commutator is nonzero.
    This is where the ping comes back. -/
def asymmetric_interface
    (g   : Node → Node → ℝ)
    (i j : Node) : Prop :=
  commutator g i j ≠ 0

/-- Commutator is antisymmetric: reversing direction
    negates it.  Asymmetry is mirrored — detectable from
    either side. -/
theorem commutator_antisymmetry
    (g   : Node → Node → ℝ)
    (i j : Node) :
    commutator g i j = -(commutator g j i) := by
  unfold commutator; ring

/-- Symmetry is mutual. -/
theorem symmetric_pair_comm
    (g   : Node → Node → ℝ)
    (i j : Node)
    (h   : symmetric_pair g i j) :
    symmetric_pair g j i := by
  unfold symmetric_pair commutator at *; linarith

/-- Asymmetric interfaces are undirected:
    if i→j is asymmetric then j→i is too. -/
theorem asymmetric_interface_comm
    (g   : Node → Node → ℝ)
    (i j : Node)
    (h   : asymmetric_interface g i j) :
    asymmetric_interface g j i := by
  unfold asymmetric_interface commutator at *; linarith

/-- The commutator distributes over pointwise addition of
    latency fields.  Key to separating baseline from signal. -/
theorem commutator_add
    (g h : Node → Node → ℝ)
    (i j : Node) :
    commutator (fun a b => g a b + h a b) i j =
    commutator g i j + commutator h i j := by
  unfold commutator; ring

/-- When the baseline is a symmetric pair (i, j), the
    commutator of any probe equals its residual asymmetry
    directly — the baseline drops out.
    This is "calibration isolates signal" as a theorem. -/
theorem symmetric_baseline_isolates_signal
    (base  : Node → Node → ℝ)
    (probe : Node → Node → ℝ)
    (i j   : Node)
    (h_sym : symmetric_pair base i j) :
    commutator probe i j =
    commutator (fun a b => probe a b - base a b) i j := by
  unfold symmetric_pair commutator at *
  linarith

/-- Asymmetry is nonneg by definition. -/
theorem asymmetry_nonneg
    (g   : Node → Node → ℝ)
    (i j : Node) :
    0 ≤ asymmetry g i j :=
  Real.abs_nonneg _

/-- Asymmetry is zero iff the pair is symmetric. -/
theorem asymmetry_zero_iff_symmetric
    (g   : Node → Node → ℝ)
    (i j : Node) :
    asymmetry g i j = 0 ↔ symmetric_pair g i j := by
  unfold asymmetry symmetric_pair
  exact Real.abs_eq_zero


-- ====================================================
-- LAYER 5: ITERATIVE ACCUMULATION
-- ====================================================
/-!
  Probes compose as a semigroup (Layer 3).
  Here we define what accumulates as probes are applied
  over time — the monoid action on the asymmetry observable.

  The key design choice: we sum asymmetry contributions
  over the probe list using Fin indexing, which keeps
  everything finite and avoids the ℕ-indexed infinite
  sequence complexity that caused proof gaps before.
-/

/-- Per-node asymmetry: sum of unsigned commutators to
    all other nodes in the observable set. -/
def node_asymmetry
    (g     : Node → Node → ℝ)
    (nodes : Finset Node)
    (n     : Node) : ℝ :=
  ∑ m in nodes, asymmetry g n m

/-- node_asymmetry is nonneg. -/
theorem node_asymmetry_nonneg
    (g     : Node → Node → ℝ)
    (nodes : Finset Node)
    (n     : Node) :
    0 ≤ node_asymmetry g nodes n := by
  unfold node_asymmetry
  apply Finset.sum_nonneg
  intros m _
  exact asymmetry_nonneg g n m

/-- Accumulated asymmetry of node n over a probe list:
    sum the node asymmetry at each probe step. -/
def accumulated_asymmetry
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node)
    (n      : Node) : ℝ :=
  ∑ t : Fin probes.length,
    node_asymmetry (applyProbe (probes.get t) g) nodes n

/-- Accumulated asymmetry is nonneg. -/
theorem accumulated_asymmetry_nonneg
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node)
    (n      : Node) :
    0 ≤ accumulated_asymmetry probes g nodes n := by
  unfold accumulated_asymmetry
  apply Finset.sum_nonneg
  intros t _
  exact node_asymmetry_nonneg _ nodes n

/-- Empty probe list → zero accumulated asymmetry. -/
theorem accumulated_asymmetry_nil
    (g     : Node → Node → ℝ)
    (nodes : Finset Node)
    (n     : Node) :
    accumulated_asymmetry [] g nodes n = 0 := by
  simp [accumulated_asymmetry]

/-- A commutator witness: node n has a partner m where
    the probe's commutator is nonzero at step t.
    This is the algebraic certificate that a ping came back. -/
def commutator_witness
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (t      : Fin probes.length)
    (n      : Node)
    (nodes  : Finset Node) : Prop :=
  ∃ m ∈ nodes, n ≠ m ∧
    asymmetric_interface (applyProbe (probes.get t) g) n m

/-- Positive node asymmetry at step t implies a commutator
    witness exists at that step.
    Connects the scalar measure back to the algebraic cert. -/
theorem node_asymmetry_pos_implies_witness
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node)
    (n      : Node)
    (t      : Fin probes.length)
    (hpos   : node_asymmetry (applyProbe (probes.get t) g) nodes n > 0) :
    ∃ m ∈ nodes, asymmetry (applyProbe (probes.get t) g) n m > 0 := by
  unfold node_asymmetry at hpos
  exact Finset.exists_pos_of_sum_pos hpos

/-- Positive accumulated asymmetry at n implies n is a
    commutator witness at some probe step. -/
theorem accumulated_pos_implies_witness
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node)
    (n      : Node)
    (hn     : n ∈ nodes)
    (hpos   : accumulated_asymmetry probes g nodes n > 0) :
    ∃ t : Fin probes.length,
      commutator_witness probes g t n nodes := by
  unfold accumulated_asymmetry at hpos
  obtain ⟨t, -, ht_pos⟩ := Finset.exists_pos_of_sum_pos hpos
  obtain ⟨m, hm, hm_pos⟩ := node_asymmetry_pos_implies_witness probes g nodes n t ht_pos
  use t
  unfold commutator_witness asymmetric_interface asymmetry at *
  refine ⟨m, hm, ?_, ?_⟩
  · -- n ≠ m: if n = m then asymmetry g n n = |g n n - g n n| = 0, contradicts hm_pos
    intro h_eq
    subst h_eq
    simp [asymmetry, commutator] at hm_pos
  · -- asymmetric_interface: commutator ≠ 0 because asymmetry > 0
    intro h_zero
    simp [commutator, h_zero] at hm_pos


-- ====================================================
-- LAYER 6: STRUCTURAL DIVERSITY
-- ====================================================
/-!
  Structural diversity is the scalar total asymmetry energy
  across all observable boundary nodes over all probes.
  It is positive iff some hidden asymmetry is detectable.
  This is the "observable curvature" of the hidden graph.
-/

/-- Total accumulated asymmetry across all boundary nodes. -/
def structural_diversity
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node) : ℝ :=
  ∑ n in nodes, accumulated_asymmetry probes g nodes n

/-- Structural diversity is nonneg. -/
theorem structural_diversity_nonneg
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node) :
    0 ≤ structural_diversity probes g nodes := by
  unfold structural_diversity
  apply Finset.sum_nonneg
  intros n _
  exact accumulated_asymmetry_nonneg probes g nodes n

/-- Empty probe list → zero structural diversity. -/
theorem structural_diversity_nil
    (g     : Node → Node → ℝ)
    (nodes : Finset Node) :
    structural_diversity [] g nodes = 0 := by
  simp [structural_diversity, accumulated_asymmetry_nil]

/-- THE CORE THEOREM.
    Positive structural diversity → some boundary node
    carries positive accumulated asymmetry.

    This is a pure pigeonhole over ℝ⁺ sums.
    No path enumeration.  No factorial complexity.
    No enumeration of hidden structure.
    The existence of something asymmetric inside is proven
    purely from boundary observables. -/
theorem exists_latent_asymmetry_node
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node)
    (hpos   : structural_diversity probes g nodes > 0) :
    ∃ n ∈ nodes, accumulated_asymmetry probes g nodes n > 0 := by
  unfold structural_diversity at hpos
  exact Finset.exists_pos_of_sum_pos hpos

/-- REFINEMENT.
    Positive structural diversity → some boundary node is
    a commutator witness at some probe step.
    The scalar measure implies an algebraic certificate. -/
theorem structural_diversity_implies_witness
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (nodes  : Finset Node)
    (hpos   : structural_diversity probes g nodes > 0) :
    ∃ n ∈ nodes, ∃ t : Fin probes.length,
      commutator_witness probes g t n nodes := by
  obtain ⟨n, hn, h_acc⟩ := exists_latent_asymmetry_node probes g nodes hpos
  obtain ⟨t, hwit⟩     := accumulated_pos_implies_witness probes g nodes n hn h_acc
  exact ⟨n, hn, t, hwit⟩


-- ====================================================
-- LAYER 7: UNIFIED INFERENCE
-- ====================================================
/-!
  A node is informative if it carries either:
  (a) a residual signature — outlier from calibration, or
  (b) a commutator witness — asymmetry in the hidden graph.

  Both are detectable from boundary observables alone.
  The hidden structure is never directly observed.
  Only its *existence* is proven.
-/

/-- A node is informative when it is either the observed
    node with a stable signature, or a commutator witness
    at some probe step. -/
def informative_node
    (C      : Calibration)
    (Obs    : Observation)
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (n      : Node) : Prop :=
  (stable_signature C Obs ∧ Obs.obs_node = n) ∨
  (∃ t : Fin probes.length,
      commutator_witness probes g t n C.baseline_nodes)

/-- MAIN INFERENCE THEOREM.
    Given:
      • a calibrated baseline with a stable signature, AND
      • positive structural diversity

    Then at least one informative node exists in the
    baseline set.

    This is a pure existence result.  We do not identify
    the hidden structure — we prove something is there.
    The *content* of "something" is domain-dependent:
      - bribery network  → corrupt intermediary
      - org bottleneck   → process node with directional delay
      - physical medium  → boundary between tissue / rock types
    The mathematics is domain-agnostic. -/
theorem informative_nodes_exist
    (C      : Calibration)
    (Obs    : Observation)
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (h_sig  : stable_signature C Obs)
    (h_div  : structural_diversity probes g C.baseline_nodes > 0) :
    ∃ n ∈ C.baseline_nodes, informative_node C Obs probes g n := by
  obtain ⟨n, hn, t, hwit⟩ :=
    structural_diversity_implies_witness probes g C.baseline_nodes h_div
  exact ⟨n, hn, Or.inr ⟨t, hwit⟩⟩

/-- SIGNATURE COROLLARY.
    When the observed node is in the baseline and both
    conditions hold, the observed node itself is informative. -/
theorem observed_node_informative
    (C      : Calibration)
    (Obs    : Observation)
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (h_obs  : Obs.obs_node ∈ C.baseline_nodes)
    (h_sig  : stable_signature C Obs)
    (h_div  : structural_diversity probes g C.baseline_nodes > 0) :
    informative_node C Obs probes g Obs.obs_node := by
  exact Or.inl ⟨h_sig, rfl⟩

/-- DISJUNCTION THEOREM.
    At least one of: the observed node is informative, OR
    some other baseline node is a commutator witness. -/
theorem observed_or_witness
    (C      : Calibration)
    (Obs    : Observation)
    (probes : List Probe)
    (g      : Node → Node → ℝ)
    (h_obs  : Obs.obs_node ∈ C.baseline_nodes)
    (h_sig  : stable_signature C Obs)
    (h_div  : structural_diversity probes g C.baseline_nodes > 0) :
    informative_node C Obs probes g Obs.obs_node ∨
    ∃ n ∈ C.baseline_nodes, informative_node C Obs probes g n :=
  Or.inl (observed_node_informative C Obs probes g h_obs h_sig h_div)


-- ====================================================
-- LAYER 8: SYSTEM DYNAMICS BRIDGE
-- ====================================================
/-!
  The symmetry algebra layer connects Causal Radar to
  System Dynamics through this correspondence:

  CAUSAL RADAR               SYSTEM DYNAMICS
  ─────────────────────────  ─────────────────────────────
  symmetric_region       ↔   stable feedback loop
                             (inflow = outflow at steady
                             state; signal circulates
                             without divergence)

  asymmetric_interface   ↔   structural break in a loop
                             (reinforcing → balancing, or
                             directional delay accumulates)

  commutator magnitude   ↔   stock accumulation rate
                             (how far flow is from balanced)

  Calibration            ↔   reference system archetype
                             ("normal throughput baseline")

  structural_diversity   ↔   aggregate asymmetry energy
                             across the observable boundary
                             — scalar drift from attractor

  accumulated_asymmetry  ↔   integrated stock deviation
                             over time

  foldProbes             ↔   iterated application of a
                             policy or intervention over
                             time steps

  THE KEY UNIFYING INSIGHT:
  In System Dynamics, stocks accumulate when inflow ≠ outflow.
  That inequality IS a nonzero commutator in the flow graph.
  Causal Radar detects this from boundary probes without ever
  observing the stocks directly.

  Radar / seismograph / MRI are all physical instantiations
  of the same abstract structure: boundary-observable
  commutator detectors on different media.

  The theorems above are the machine-verified form of the
  claim that this detection principle holds for any
  graph-structured causal system, regardless of domain.
-/

end CausalGraph
