import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CausalSystem

variable {Node : Type} [Fintype Node] [DecidableEq Node]

/-! ### Time-varying graph: edge weights depend on a time index -/
structure Graph (Node : Type) where
  /-- Causal weight of edge (u → v) at time t -/
  weight     : ℕ → Node → Node → ℚ
  /-- Epistemic confidence in that edge (0 = pure hypothesis, 1 = well established) -/
  confidence : ℕ → Node → Node → ℚ
  weight_nn      : ∀ t u v, 0 ≤ weight t u v
  confidence_nn  : ∀ t u v, 0 ≤ confidence t u v
  confidence_le  : ∀ t u v, confidence t u v ≤ 1

/-! ### Bottleneck / hub designation -/
structure Observer (Node : Type) where
  obs         : Finset Node
  /-- Nodes flagged as high-connectivity bottlenecks (e.g. gut lining) -/
  bottlenecks : Finset Node

/-! ### Pathway identity – which causal route a trajectory represents -/
inductive PathwayKind where
  | GutVagus    -- long slow route via vagus nerve
  | OralCranial -- shorter dental / cranial nerve route
  | Unknown
  deriving DecidableEq, Repr

/-! ### Trajectory now carries a time-stamp and pathway tag -/
structure TaggedTraj (Node : Type) (n : ℕ) where
  nodes   : Fin n → Node
  start_t : ℕ                -- absolute time when trajectory begins
  pathway : PathwayKind

abbrev Trajectory (Node : Type) (n : ℕ) := Fin n → Node

/-! ### Validity at a given start time -/
def valid_traj (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n) : Bool :=
  match n with
  | 0     => false
  | _ + 1 => Finset.univ.all fun i : Fin _ =>
               G.weight (start_t + i.val) (t i.castSucc) (t i.succ) > 0

/-! ### Last-node observation -/
def terminates_in_observer
    (O : Observer Node) {n : ℕ} (t : Trajectory Node n) : Bool :=
  match n with
  | 0     => false
  | n + 1 => decide (t ⟨n, Nat.lt_succ_self n⟩ ∈ O.obs)

/-! ### Does the trajectory pass through a bottleneck node? -/
def passes_through_bottleneck
    (O : Observer Node) {n : ℕ} (t : Trajectory Node n) : Bool :=
  Finset.univ.any fun i : Fin n => decide (t i ∈ O.bottlenecks)

/-! ### Trajectory weight at a given start time -/
def traj_weight (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n) : ℚ :=
  match n with
  | 0     => 0
  | 1     => 1
  | n + 2 => Finset.univ.prod fun i : Fin (n + 1) =>
               G.weight (start_t + i.val) (t i.castSucc) (t i.succ)

/-! ### Confidence-weighted trajectory score -/
def traj_confidence (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n) : ℚ :=
  match n with
  | 0     => 0
  | 1     => 1
  | n + 2 => Finset.univ.prod fun i : Fin (n + 1) =>
               G.confidence (start_t + i.val) (t i.castSucc) (t i.succ)

/-! ### Observable flow (time-aware) -/
def observable_flow (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) : ℚ :=
  ∑ n : Fin (N + 1),
    ∑ t : Trajectory Node n.val,
      if valid_traj G start_t t && terminates_in_observer O t
      then traj_weight G start_t t
      else 0

/-! ### Total flow (time-aware) -/
def total_flow (G : Graph Node) (start_t N : ℕ) : ℚ :=
  ∑ n : Fin (N + 1),
    ∑ t : Trajectory Node n.val,
      if valid_traj G start_t t
      then traj_weight G start_t t
      else 0

/-! ### Bottleneck flow: trajectories that pass through a bottleneck hub -/
def bottleneck_flow (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) : ℚ :=
  ∑ n : Fin (N + 1),
    ∑ t : Trajectory Node n.val,
      if valid_traj G start_t t && passes_through_bottleneck O t
      then traj_weight G start_t t
      else 0

/-! ### Pathway-specific flow -/
def pathway_flow (G : Graph Node) (O : Observer Node)
    (pk : PathwayKind) (start_t N : ℕ)
    (label : Trajectory Node → ℕ → PathwayKind) : ℚ :=
  ∑ n : Fin (N + 1),
    ∑ t : Trajectory Node n.val,
      if valid_traj G start_t t &&
         decide (label t n.val = pk)
      then traj_weight G start_t t
      else 0

/-! ### Key lemmas -/

lemma traj_weight_nonneg (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n)
    (hv : valid_traj G start_t t = true) : 0 ≤ traj_weight G start_t t := by
  match n with
  | 0 => simp [valid_traj] at hv
  | 1 => simp [traj_weight]
  | n + 2 =>
    simp [traj_weight]
    apply Finset.prod_nonneg
    intro i _
    exact G.weight_nn _ _ _

lemma traj_confidence_nonneg (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n) : 0 ≤ traj_confidence G start_t t := by
  match n with
  | 0 => simp [traj_confidence]
  | 1 => simp [traj_confidence]
  | n + 2 =>
    simp [traj_confidence]
    apply Finset.prod_nonneg
    intro i _
    exact G.confidence_nn _ _ _

lemma traj_confidence_le_one (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n) : traj_confidence G start_t t ≤ 1 := by
  match n with
  | 0 => simp [traj_confidence]
  | 1 => simp [traj_confidence]
  | n + 2 =>
    simp [traj_confidence]
    apply Finset.prod_le_one
    · intro i _; exact G.confidence_nn _ _ _
    · intro i _; exact G.confidence_le _ _ _

lemma observable_flow_nonneg (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) : 0 ≤ observable_flow G O start_t N := by
  apply Finset.sum_nonneg; intro n _
  apply Finset.sum_nonneg; intro t _
  split_ifs with h
  · simp [Bool.and_eq_true] at h
    exact traj_weight_nonneg G start_t t h.1
  · simp

lemma total_flow_nonneg (G : Graph Node) (start_t N : ℕ) :
    0 ≤ total_flow G start_t N := by
  apply Finset.sum_nonneg; intro n _
  apply Finset.sum_nonneg; intro t _
  split_ifs with h
  · exact traj_weight_nonneg G start_t t h
  · simp

lemma observable_flow_le_total (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) :
    observable_flow G O start_t N ≤ total_flow G start_t N := by
  apply Finset.sum_le_sum; intro n _
  apply Finset.sum_le_sum; intro t _
  split_ifs with h
  · simp [Bool.and_eq_true] at h
    simp [h.1, traj_weight_nonneg G start_t t h.1]
  · simp

lemma bottleneck_flow_le_total (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) :
    bottleneck_flow G O start_t N ≤ total_flow G start_t N := by
  apply Finset.sum_le_sum; intro n _
  apply Finset.sum_le_sum; intro t _
  split_ifs with h
  · simp [Bool.and_eq_true] at h
    simp [h.1, traj_weight_nonneg G start_t t h.1]
  · simp

/-! ### Probability -/

def path_probability (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) (h : total_flow G start_t N ≠ 0) : ℚ :=
  observable_flow G O start_t N / total_flow G start_t N

lemma path_probability_nonneg (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) (h : total_flow G start_t N ≠ 0)
    (hpos : 0 < total_flow G start_t N) :
    0 ≤ path_probability G O start_t N h := by
  rw [path_probability]
  apply div_nonneg
  · exact observable_flow_nonneg G O start_t N
  · exact le_of_lt hpos

lemma path_probability_le_one (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) (h : total_flow G start_t N ≠ 0)
    (hpos : 0 < total_flow G start_t N) :
    path_probability G O start_t N h ≤ 1 := by
  rw [path_probability, div_le_one hpos]
  exact observable_flow_le_total G O start_t N

/-! ### Bottleneck probability: how much flow passes through the hub -/

def bottleneck_probability (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) (h : total_flow G start_t N ≠ 0) : ℚ :=
  bottleneck_flow G O start_t N / total_flow G start_t N

lemma bottleneck_probability_le_one (G : Graph Node) (O : Observer Node)
    (start_t N : ℕ) (h : total_flow G start_t N ≠ 0)
    (hpos : 0 < total_flow G start_t N) :
    bottleneck_probability G O start_t N h ≤ 1 := by
  rw [bottleneck_probability, div_le_one hpos]
  exact bottleneck_flow_le_total G O start_t N

/-! ### Time-window flow: sum over a range of start times
    Models population flux — the edge weight oscillates, so we integrate
    over a window [t0, t0 + T) to get the aggregate exposure. -/

def windowed_flow (G : Graph Node) (O : Observer Node)
    (t0 T N : ℕ) : ℚ :=
  ∑ τ : Fin T, observable_flow G O (t0 + τ.val) N

def windowed_total (G : Graph Node) (t0 T N : ℕ) : ℚ :=
  ∑ τ : Fin T, total_flow G t0 N

lemma windowed_flow_nonneg (G : Graph Node) (O : Observer Node)
    (t0 T N : ℕ) : 0 ≤ windowed_flow G O t0 T N := by
  apply Finset.sum_nonneg; intro τ _
  exact observable_flow_nonneg G O (t0 + τ.val) N

/-! ### Pathway fingerprint score
    Given a trajectory, score it as consistent with a pathway by
    combining causal weight with epistemic confidence. -/

def fingerprint_score (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n) : ℚ :=
  traj_weight G start_t t * traj_confidence G start_t t

lemma fingerprint_score_nonneg (G : Graph Node) (start_t : ℕ) {n : ℕ}
    (t : Trajectory Node n)
    (hv : valid_traj G start_t t = true) :
    0 ≤ fingerprint_score G start_t t := by
  apply mul_nonneg
  · exact traj_weight_nonneg G start_t t hv
  · exact traj_confidence_nonneg G start_t t

/-! ### Comparative pathway likelihood
    Given two pathway flows, which is more probable? -/

def pathway_more_likely (flowA flowB : ℚ) : Bool :=
  flowA > flowB

/-! ### Edge silence: an edge is "silent" at time t if its weight is zero -/

def edge_silent (G : Graph Node) (t : ℕ) (u v : Node) : Prop :=
  G.weight t u v = 0

instance (G : Graph Node) (t : ℕ) (u v : Node) :
    Decidable (edge_silent G t u v) :=
  inferInstance

/-! ### A node is a bottleneck if it appears in every valid trajectory
    of length ≥ 2 between two given nodes (structural bottleneck).
    Here we state a simpler observational version: the node is designated
    as a bottleneck in the Observer. -/

def is_bottleneck (O : Observer Node) (v : Node) : Prop :=
  v ∈ O.bottlenecks

instance (O : Observer Node) (v : Node) : Decidable (is_bottleneck O v) :=
  inferInstance

end CausalSystem
