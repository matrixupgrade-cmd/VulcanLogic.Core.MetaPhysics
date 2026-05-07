import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
open Finset Classical

variable (Node : Type) [Fintype Node] [DecidableEq Node]

abbrev Edge := Node → Node → Prop

structure Graph where
  edge : Edge Node

abbrev GraphTrace (Node : Type) [Fintype Node] := ℕ → Graph Node
abbrev Basin (Node : Type) := Finset Node

def project_graph
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (G : Graph Node) : Graph Node :=
  { edge := fun i j => i ∉ B ∧ j ∉ B ∧ G.edge i j }

def obs_equiv
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (G₁ G₂ : Graph Node) : Prop :=
  project_graph B G₁ = project_graph B G₂

def hidden_difference
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (G₁ G₂ : Graph Node) : Prop :=
  ∀ i j, i ∉ B → j ∉ B → G₁.edge i j ↔ G₂.edge i j

def basin_escape
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (G₁ G₂ : Graph Node) : Prop :=
  ∃ i j, i ∉ B ∧ j ∉ B ∧ G₁.edge i j ≠ G₂.edge i j

def observable_distance
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (G₁ G₂ : Graph Node) : ℕ :=
  ∑ i, ∑ j,
    if i ∉ B ∧ j ∉ B ∧ G₁.edge i j ≠ G₂.edge i j then 1 else 0

/-! ## Temporal causal structure -/

def monotone_trace
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T : GraphTrace Node) : Prop :=
  ∀ n i j, T n |>.edge i j → T (n + 1) |>.edge i j

def basin_masks
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (T₁ T₂ : GraphTrace Node) (k : ℕ) : Prop :=
  ∀ n < k, obs_equiv B (T₁ n) (T₂ n)

/-! ## Monotone propagation lemma -/

lemma monotone_edge_persist
    {Node : Type} [Fintype Node] [DecidableEq Node]
    {T : GraphTrace Node}
    (mono : monotone_trace T)
    {i j : Node} {k : ℕ}
    (h : T k |>.edge i j) :
    ∀ n ≥ k, T n |>.edge i j := by
  intro n hn
  induction n with
  | zero =>
      have : k = 0 := Nat.eq_zero_of_le_zero hn
      rwa [← this]
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · exact h
      · exact mono n i j (ih (Nat.lt_succ_iff.mp hlt))

/-! ## Symmetric escape persistence -/

theorem escape_persists_under_monotone_sym
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (mono₁ : monotone_trace T₁)
    (mono₂ : monotone_trace T₂)
    (h_asym₁ : ∀ n i j, T₁ n |>.edge i j → ¬ T₂ n |>.edge i j →
                          ¬ T₂ (n+1) |>.edge i j)
    (h_asym₂ : ∀ n i j, T₂ n |>.edge i j → ¬ T₁ n |>.edge i j →
                          ¬ T₁ (n+1) |>.edge i j)
    (k : ℕ)
    (h_escape : basin_escape B (T₁ k) (T₂ k)) :
    ∀ n ≥ k, basin_escape B (T₁ n) (T₂ n) := by
  obtain ⟨i, j, hi, hj, hdiff⟩ := h_escape
  intro n hn
  rcases Classical.em (T₁ k |>.edge i j) with h₁ | h₁
  · have h₂ : ¬ T₂ k |>.edge i j := by
      intro h
      apply hdiff
      ext
      constructor <;> intro _ <;> assumption
    have h₁n : T₁ n |>.edge i j :=
      monotone_edge_persist mono₁ h₁ n hn
    have h₂n : ¬ T₂ n |>.edge i j := by
      induction n with
      | zero =>
          rwa [← Nat.eq_zero_of_le_zero hn]
      | succ n ih =>
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact h₂
          · exact h_asym₁ n i j
              (monotone_edge_persist mono₁ h₁ n (Nat.lt_succ_iff.mp hlt))
              (ih (Nat.lt_succ_iff.mp hlt))
    exact ⟨i, j, hi, hj, by
      intro heq
      exact h₂n (heq ▸ h₁n)⟩
  · have h₂ : T₂ k |>.edge i j := by
      rcases Classical.em (T₂ k |>.edge i j) with h | h
      · exact h
      · exfalso
        apply hdiff
        ext
        constructor
        · intro hc
          exact absurd hc h₁
        · intro hc
          exact absurd hc h
    have h₂n : T₂ n |>.edge i j :=
      monotone_edge_persist mono₂ h₂ n hn
    have h₁n : ¬ T₁ n |>.edge i j := by
      induction n with
      | zero =>
          rwa [← Nat.eq_zero_of_le_zero hn]
      | succ n ih =>
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact h₁
          · exact h_asym₂ n i j
              (monotone_edge_persist mono₂ h₂ n (Nat.lt_succ_iff.mp hlt))
              (ih (Nat.lt_succ_iff.mp hlt))
    exact ⟨i, j, hi, hj, by
      intro heq
      exact h₁n (heq.symm ▸ h₂n)⟩

/-! ## Gateway structure -/

/--
Nodes capable of participating in observable escape at time k.
These are admissible hidden routing nodes.
-/
def gateway_region
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ) : Finset Node :=
  Finset.univ.filter (fun g =>
    ∃ o,
      T₁ k |>.edge g o ≠ T₂ k |>.edge g o)

/--
A gateway node routes a differing signal to an outcome node.
-/
def routes_escape
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (g o : Node) : Prop :=
  T₁ k |>.edge g o ≠ T₂ k |>.edge g o

/-!
## Forced gateway overlap theorem

If the number of observable independent escape outcomes exceeds
the number of admissible gateway nodes, then some gateway node
must route escape signals to multiple outcomes.

This is the finite-capacity structural guarantee underlying
hidden causal overlap inference.
-/

theorem forced_gateway_overlap
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (m : ℕ)
    (hm : m > 0)
    (outcomes : Fin m → Node)
    (h_escapes :
      ∀ idx : Fin m,
        ∃ g : Node,
          g ∈ gateway_region B T₁ T₂ k ∧
          routes_escape T₁ T₂ k g (outcomes idx))
    (h_small :
      (gateway_region B T₁ T₂ k).card < m) :
    ∃ g : Node,
      g ∈ gateway_region B T₁ T₂ k ∧
      ∃ i j : Fin m,
        i ≠ j ∧
        routes_escape T₁ T₂ k g (outcomes i) ∧
        routes_escape T₁ T₂ k g (outcomes j) := by

  let f : Fin m → gateway_region B T₁ T₂ k :=
    fun idx =>
      let ⟨g, hg, _⟩ := h_escapes idx
      ⟨g, hg⟩

  have h_not_injective : ¬ Function.Injective f := by
    intro h_inj

    have h_card_le :
        m ≤ (gateway_region B T₁ T₂ k).card := by
      simpa using Fintype.card_le_of_injective f h_inj

    exact Nat.not_le_of_gt h_small h_card_le

  obtain ⟨i, j, hij, hsame⟩ :=
    not_function_injective_iff.mp h_not_injective

  have hfi : (f i).1 = (f j).1 := by
    exact congrArg Subtype.val hsame

  let g := (f i).1

  have hg_mem : g ∈ gateway_region B T₁ T₂ k := by
    exact (f i).2

  have hi_escape :
      routes_escape T₁ T₂ k g (outcomes i) := by
    rcases h_escapes i with ⟨g', hg', hroute⟩
    dsimp [g]
    simpa [f] using hroute

  have hj_escape :
      routes_escape T₁ T₂ k g (outcomes j) := by
    rcases h_escapes j with ⟨g', hg', hroute⟩
    dsimp [g]
    simpa [f, hfi] using hroute

  refine ⟨g, hg_mem, i, j, hij, hi_escape, hj_escape⟩
