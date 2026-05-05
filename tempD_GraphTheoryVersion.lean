import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CausalSystem

variable {Node : Type} [Fintype Node] [DecidableEq Node]

structure Graph (Node : Type) where
  weight : Node → Node → ℚ

structure Observer (Node : Type) where
  obs : Finset Node

abbrev Trajectory (Node : Type) (n : ℕ) := Fin n → Node

/-! ### Validity: Bool-valued for Decidability -/

def valid_traj (G : Graph Node) {n : ℕ} (t : Trajectory Node n) : Bool :=
  match n with
  | 0     => false
  | _ + 1 => Finset.univ.all fun i : Fin _ =>
               G.weight (t i.castSucc) (t i.succ) > 0

/-! ### Last-node observation: no positivity hypothesis needed -/

def terminates_in_observer
    (O : Observer Node) {n : ℕ} (t : Trajectory Node n) : Bool :=
  match n with
  | 0     => false
  | n + 1 => decide (t ⟨n, Nat.lt_succ_self n⟩ ∈ O.obs)

/-! ### Trajectory weight -/

def traj_weight (G : Graph Node) {n : ℕ} (t : Trajectory Node n) : ℚ :=
  match n with
  | 0     => 0
  | 1     => 1
  | n + 2 => Finset.univ.prod fun i : Fin (n + 1) =>
               G.weight (t i.castSucc) (t i.succ)

/-! ### Flows -/

def observable_flow (G : Graph Node) (O : Observer Node) (N : ℕ) : ℚ :=
  ∑ n : Fin (N + 1),
    ∑ t : Trajectory Node n.val,
      if valid_traj G t && terminates_in_observer O t
      then traj_weight G t
      else 0

def total_flow (G : Graph Node) (N : ℕ) : ℚ :=
  ∑ n : Fin (N + 1),
    ∑ t : Trajectory Node n.val,
      if valid_traj G t
      then traj_weight G t
      else 0

/-! ### Key lemmas needed before probability is meaningful -/

lemma traj_weight_nonneg {G : Graph Node} {n : ℕ} (t : Trajectory Node n)
    (hv : valid_traj G t = true) : 0 ≤ traj_weight G t := by
  match n with
  | 0 => simp [valid_traj] at hv
  | 1 => simp [traj_weight]
  | n + 2 =>
    simp [traj_weight]
    apply Finset.prod_nonneg
    intro i _
    simp [valid_traj, Finset.all_iff_forall] at hv
    exact le_of_lt (hv i)

lemma observable_flow_le_total (G : Graph Node) (O : Observer Node) (N : ℕ) :
    observable_flow G O N ≤ total_flow G N := by
  apply Finset.sum_le_sum; intro n _
  apply Finset.sum_le_sum; intro t _
  split_ifs with h
  · simp [Bool.and_eq_true] at h
    simp [h.1, traj_weight_nonneg t h.1]
  · simp

/-! ### Probability -/

def path_probability (G : Graph Node) (O : Observer Node) (N : ℕ)
    (h : total_flow G N ≠ 0) : ℚ :=
  observable_flow G O N / total_flow G N

lemma path_probability_le_one (G : Graph Node) (O : Observer Node) (N : ℕ)
    (h : total_flow G N ≠ 0)
    (hpos : 0 < total_flow G N) : path_probability G O N h ≤ 1 := by
  rw [path_probability, div_le_one hpos]
  exact observable_flow_le_total G O N

end CausalSystem
