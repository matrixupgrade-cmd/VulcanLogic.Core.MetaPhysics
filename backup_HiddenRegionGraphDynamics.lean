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

/-! ## Escape persistence -/

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
      simp [*]
    have h₁n := monotone_edge_persist mono₁ h₁ n hn
    have h₂n : ¬ T₂ n |>.edge i j := by
      induction n with
      | zero => simpa [hn] using h₂
      | succ n ih =>
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact h₂
          · exact h_asym₁ n i j
              (monotone_edge_persist mono₁ h₁ n (Nat.lt_succ_iff.mp hlt))
              (ih (Nat.lt_succ_iff.mp hlt))
    exact ⟨i, j, hi, hj, by intro h; exact h₂n (h ▸ h₁n)⟩
  · have h₂ : T₂ k |>.edge i j := by
      rcases Classical.em (T₂ k |>.edge i j) with h | h
      · exact h
      · exfalso
        apply hdiff
        simp [*]
    have h₂n := monotone_edge_persist mono₂ h₂ n hn
    have h₁n : ¬ T₁ n |>.edge i j := by
      induction n with
      | zero => simpa [hn] using h₁
      | succ n ih =>
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact h₁
          · exact h_asym₂ n i j
              (monotone_edge_persist mono₂ h₂ n (Nat.lt_succ_iff.mp hlt))
              (ih (Nat.lt_succ_iff.mp hlt))
    exact ⟨i, j, hi, hj, by intro h; exact h₁n (h.symm ▸ h₂n)⟩

/-! ## Gateway structure -/

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

/-! ## Pigeonhole -/

private lemma not_injective_collision
    {α : Type} {m : ℕ} {S : Finset α}
    (f : Fin m → α)
    (hf : ∀ i, f i ∈ S)
    (h_small : S.card < m) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  by_contra h
  push_neg at h
  have inj : Function.Injective f := by
    intro a b hfab
    by_contra hne
    exact h a b hne hfab
  have hcard :=
    Fintype.card_le_of_injective
      (fun i : Fin m => ⟨f i, hf i⟩)
      (by intro a b h; exact inj (Subtype.mk.inj h))
  simpa [Fintype.card_fin] using hcard

theorem forced_gateway_overlap
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (m : ℕ) (hm : m > 0)
    (outcomes : Fin m → Node)
    (h_escapes : ∀ i,
      ∃ g, g ∈ gateway_region B T₁ T₂ k ∧
           routes_escape T₁ T₂ k g (outcomes i))
    (h_small : (gateway_region B T₁ T₂ k).card < m) :
    ∃ g,
      g ∈ gateway_region B T₁ T₂ k ∧
      ∃ i j : Fin m,
        i ≠ j ∧
        routes_escape T₁ T₂ k g (outcomes i) ∧
        routes_escape T₁ T₂ k g (outcomes j) := by
  choose gw hmem hroutes using h_escapes
  obtain ⟨i, j, hij, heq⟩ :=
    not_injective_collision gw hmem h_small
  exact ⟨gw i, hmem i, i, j, hij, hroutes i, heq ▸ hroutes j⟩

/-! ## FIXED causal identification -/

theorem causal_gateway_identification_fixed
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
    (h_masked : basin_masks B T₁ T₂ k)
    (m : ℕ) (hm : m > 0)
    (outcomes : Fin m → Node)
    (h_out : ∀ i, outcomes i ∉ B)
    (h_escapes : ∀ i,
      ∃ g, g ∈ gateway_region B T₁ T₂ k ∧
           routes_escape T₁ T₂ k g (outcomes i))
    (h_small : (gateway_region B T₁ T₂ k).card < m)
    (h_dom :
      ∀ g ∈ gateway_region B T₁ T₂ k,
        (∃ i j : Fin m, i ≠ j ∧
          routes_escape T₁ T₂ k g (outcomes i) ∧
          routes_escape T₁ T₂ k g (outcomes j)) →
        ∀ idx, routes_escape T₁ T₂ k g (outcomes idx)) :
    ∃ g,
      g ∈ gateway_region B T₁ T₂ k ∧
      ∀ idx, routes_escape T₁ T₂ k g (outcomes idx) := by
  obtain ⟨g, hg, i, j, hij, hi, hj⟩ :=
    forced_gateway_overlap B T₁ T₂ k m hm outcomes h_escapes h_small
  have hall := h_dom g hg ⟨i, j, hij, hi, hj⟩
  exact ⟨g, hg, hall⟩
