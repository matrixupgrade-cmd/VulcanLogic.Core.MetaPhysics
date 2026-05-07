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

/-! ## Temporal structure -/

def monotone_trace
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T : GraphTrace Node) : Prop :=
  ∀ n i j, T n |>.edge i j → T (n + 1) |>.edge i j

def basin_masks
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (T₁ T₂ : GraphTrace Node) (k : ℕ) : Prop :=
  ∀ n < k, obs_equiv B (T₁ n) (T₂ n)

/-! ## Persistence -/

lemma monotone_edge_persist
    {Node : Type} [Fintype Node] [DecidableEq Node]
    {T : GraphTrace Node}
    (mono : monotone_trace T)
    {i j : Node} {k n : ℕ}
    (h : T k |>.edge i j)
    (hn : n ≥ k) :
    T n |>.edge i j := by
  induction n with
  | zero => cases k <;> simp at hn <;> simpa using h
  | succ n ih =>
      by_cases hnk : n + 1 = k
      · cases hnk; exact h
      · have hle : k ≤ n := by
          by_contra hlt
          have := Nat.le_of_not_lt hlt
          exact hnk (Nat.succ_le_of_lt this)
        exact mono n i j (ih hle (by omega))

/-! ## Gateway region -/

def gateway_region
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ) : Finset Node :=
  Finset.univ.filter (fun g =>
    ∃ o, T₁ k |>.edge g o ≠ T₂ k |>.edge g o)

def routes_escape
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (g o : Node) : Prop :=
  T₁ k |>.edge g o ≠ T₂ k |>.edge g o

/-! ## Pigeonhole core -/

lemma not_injective_collision
    {α : Type} {m : ℕ} {S : Finset α}
    (f : Fin m → α)
    (hf : ∀ i, f i ∈ S)
    (hsmall : S.card < m) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  by_contra h
  push_neg at h
  have hinj : Function.Injective f := by
    intro a b heq
    by_contra hne
    exact absurd heq (h a b hne)
  have hcard : m ≤ S.card := by
    have := Fintype.card_le_of_injective
      (fun i : Fin m => ⟨f i, hf i⟩)
      (fun a b h => hinj (Subtype.mk.inj h))
    simpa [Fintype.card_fin] using this
  exact Nat.not_le.mpr hsmall hcard

/-! ## Forced gateway overlap -/

theorem forced_gateway_overlap
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k m : ℕ)
    (hm : m > 0)
    (outcomes : Fin m → Node)
    (hesc : ∀ i, ∃ g,
      g ∈ gateway_region B T₁ T₂ k ∧
      routes_escape T₁ T₂ k g (outcomes i))
    (hsmall : (gateway_region B T₁ T₂ k).card < m) :
    ∃ g i j,
      i ≠ j ∧
      g ∈ gateway_region B T₁ T₂ k ∧
      routes_escape T₁ T₂ k g (outcomes i) ∧
      routes_escape T₁ T₂ k g (outcomes j) := by
  choose gw hgw using hesc
  obtain ⟨i, j, hij, heq⟩ :=
    not_injective_collision gw (by intro i; exact (hgw i).1) hsmall
  exact ⟨gw i, i, j, hij, (hgw i).1, (hgw i).2, heq ▸ (hgw j).2⟩
