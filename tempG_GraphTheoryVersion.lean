import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
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
  · have h₂ : ¬ T₂ k |>.edge i j :=
      fun h => hdiff (propext ⟨fun _ => h, fun _ => h₁⟩)
    have h₁n : T₁ n |>.edge i j := monotone_edge_persist mono₁ h₁ n hn
    have h₂n : ¬ T₂ n |>.edge i j := by
      induction n with
      | zero => rwa [← Nat.eq_zero_of_le_zero hn]
      | succ n ih =>
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact h₂
          · exact h_asym₁ n i j
              (monotone_edge_persist mono₁ h₁ n (Nat.lt_succ_iff.mp hlt))
              (ih (Nat.lt_succ_iff.mp hlt))
    exact ⟨i, j, hi, hj, fun heq => h₂n (heq ▸ h₁n)⟩
  · have h₂ : T₂ k |>.edge i j := by
      rcases Classical.em (T₂ k |>.edge i j) with h | h
      · exact h
      · exact absurd (propext ⟨fun hc => absurd hc h₁, fun hc => absurd hc h⟩) hdiff
    have h₂n : T₂ n |>.edge i j := monotone_edge_persist mono₂ h₂ n hn
    have h₁n : ¬ T₁ n |>.edge i j := by
      induction n with
      | zero => rwa [← Nat.eq_zero_of_le_zero hn]
      | succ n ih =>
          rcases Nat.eq_or_lt_of_le hn with rfl | hlt
          · exact h₁
          · exact h_asym₂ n i j
              (monotone_edge_persist mono₂ h₂ n (Nat.lt_succ_iff.mp hlt))
              (ih (Nat.lt_succ_iff.mp hlt))
    exact ⟨i, j, hi, hj, fun heq => h₁n (heq.symm ▸ h₂n)⟩

/-! ## Phase transition theorem: causal revelation -/

theorem causal_revelation_graph
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (mono₁ : monotone_trace T₁)
    (mono₂ : monotone_trace T₂)
    (k : ℕ)
    (h_masked : basin_masks B T₁ T₂ k)
    (h_escape : basin_escape B (T₁ k) (T₂ k))
    (h_asym₁ : ∀ n i j, T₁ n |>.edge i j → ¬ T₂ n |>.edge i j →
                          ¬ T₂ (n+1) |>.edge i j)
    (h_asym₂ : ∀ n i j, T₂ n |>.edge i j → ¬ T₁ n |>.edge i j →
                          ¬ T₁ (n+1) |>.edge i j) :
    (∀ n < k, observable_distance B (T₁ n) (T₂ n) = 0) ∧
    (∀ n ≥ k, observable_distance B (T₁ n) (T₂ n) > 0) := by
  constructor
  · intro n hn
    have heq := h_masked n hn
    unfold observable_distance obs_equiv project_graph at *
    simp only [Graph.mk.injEq] at heq
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    simp only [ite_eq_right_iff]
    intro ⟨hi, hj, hdiff⟩
    exact absurd (heq ▸ rfl) (by simp [hi, hj, hdiff])
  · intro n hn
    obtain ⟨i, j, hi, hj, hdiff⟩ := h_escape
    obtain ⟨i', j', hi', hj', hdiff_n⟩ :=
      escape_persists_under_monotone_sym B T₁ T₂ mono₁ mono₂
        h_asym₁ h_asym₂ k ⟨i, j, hi, hj, hdiff⟩ n hn
    unfold observable_distance
    apply Nat.lt_of_lt_of_le Nat.zero_lt_one
    calc 1 = if i' ∉ B ∧ j' ∉ B ∧ T₁ n |>.edge i' j' ≠ T₂ n |>.edge i' j'
              then 1 else 0 := by simp [hi', hj', hdiff_n]
         _ ≤ ∑ j'', if i' ∉ B ∧ j'' ∉ B ∧ T₁ n |>.edge i' j'' ≠ T₂ n |>.edge i' j''
                    then 1 else 0 :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) _ (Finset.mem_univ j')
         _ ≤ ∑ i'', ∑ j'', if i'' ∉ B ∧ j'' ∉ B ∧ T₁ n |>.edge i'' j'' ≠ T₂ n |>.edge i'' j''
                             then 1 else 0 :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) _ (Finset.mem_univ i')

/-!
  ## Causal Gateway Identification

  The core new conjecture.

  The intuition: if k *independent* outcome nodes all show basin escape
  at the same time, then there must exist a hidden gateway node — a node
  inside or at the boundary of the basin — whose causal signal is routing
  through to all of them simultaneously.

  We are NOT claiming to identify the root cause.
  We ARE claiming to prove the necessary existence of an intermediary node
  through which the causal signal must pass to produce this pattern of
  correlated escapes.

  This is the formal analog of Sherlock's reasoning:
  enough independent co-varying observations force the existence of
  a common hidden node — not by correlation implying causation,
  but by the graph topology being the only structure that could
  produce simultaneous escape across independent outcome nodes.

  Key definitions needed:
  - `routes_through`: node g routes signal to outcome node o in trace T
  - `independent_outcomes`: the k outcome nodes draw on genuinely
    separate causal pathways (no shared outside-basin edges except
    possibly through the gateway)
  - The conclusion: a gateway node g exists in or at the boundary
    of B such that all escape signals route through g.

  Current status: stated as `sorry` / axiom pending formal proof.
  Lean will accept the statement; the proof obligations are made explicit
  below so we know exactly what remains to be shown.
-/

/-- A node `g` routes a causal signal to outcome node `o` in trace `T`
    at time `n` if there is a directed edge from `g` to `o` in the graph. -/
def routes_through
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T : GraphTrace Node) (n : ℕ) (g o : Node) : Prop :=
  T n |>.edge g o

/-- k outcome nodes are independent with respect to basin B and traces T₁ T₂
    if no two of them share an outside-basin edge witness for their escape.
    This means their escape signals are drawing on genuinely distinct
    causal pathways — they are not just recounting the same evidence. -/
def independent_escapes
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node) (T₁ T₂ : GraphTrace Node) (n : ℕ)
    (k : ℕ) (outcomes : Fin k → Node) : Prop :=
  -- Each outcome node participates in a distinct escape edge
  (∀ m : Fin k, outcomes m ∉ B) ∧
  -- The escape edges witnessing each outcome are pairwise distinct
  (∀ m₁ m₂ : Fin k, m₁ ≠ m₂ →
    ∀ i, ¬ (T₁ n |>.edge i (outcomes m₁) ≠ T₂ n |>.edge i (outcomes m₁) ∧
             T₁ n |>.edge i (outcomes m₂) ≠ T₂ n |>.edge i (outcomes m₂)))

/-- The causal gateway identification conjecture.

    If:
    - Two traces were observationally equivalent up to time k (basin_masks)
    - At time k, k independent outcome nodes all show basin escape
    - The traces are monotone and attractors are genuinely separated
    - The k outcome nodes are independent (drawing on distinct causal paths)

    Then:
    - There exists a gateway node g (at or inside the basin boundary)
      such that g routes signal to all k outcome nodes in at least one trace.

    This is the existence proof that abductive inference is valid:
    the pattern of correlated independent escapes FORCES the existence
    of a gateway node. We are not guessing — the topology requires it.
-/
theorem causal_gateway_identification
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
    -- The number of independent outcome nodes witnessing escape
    (m : ℕ) (hm : m > 0)
    -- The outcome nodes themselves
    (outcomes : Fin m → Node)
    -- Each outcome shows basin escape at time k
    (h_escapes : ∀ idx : Fin m,
      ∃ src : Node, src ∉ B ∧
        T₁ k |>.edge src (outcomes idx) ≠ T₂ k |>.edge src (outcomes idx))
    -- The escapes are independent — distinct causal pathways
    (h_independent : independent_escapes B T₁ T₂ k m outcomes) :
    -- Conclusion: a gateway node exists that routes to all outcome nodes
    -- in at least one of the traces at time k.
    -- This is the node the observer should measure next.
    ∃ gateway : Node,
      (∀ idx : Fin m, routes_through T₁ k gateway (outcomes idx)) ∨
      (∀ idx : Fin m, routes_through T₂ k gateway (outcomes idx)) := by
  -- Proof obligation: show that independent simultaneous escapes
  -- cannot arise from distinct hidden sources — they must share a
  -- common ancestor (the gateway) by the pigeonhole principle on
  -- the basin boundary nodes.
  --
  -- The key steps that remain to be formalized:
  -- 1. Each escape at outcome idx witnesses an edge src_idx → outcomes idx
  --    where src_idx differs between T₁ and T₂.
  -- 2. By basin_masks, all src_idx must be inside or at the basin boundary
  --    (otherwise escape would have been visible before k).
  -- 3. Since m escapes are independent and the basin is finite (Fintype Node),
  --    by pigeonhole there exists a node g that is the common source.
  -- 4. g routes to all m outcome nodes in the trace that "leads" the escape.
  --
  -- This is left as sorry pending the pigeonhole formalization,
  -- which requires a finite counting argument on basin boundary nodes.
  -- The statement itself is what Lean checks — the proof gap is explicit.
  sorry

/-!
  ## What Lean is telling us

  The `sorry` above is honest — Lean accepts the *statement* of
  causal_gateway_identification as well-typed and meaningful.
  What remains is the pigeonhole argument on finite basin boundary nodes.

  The critical insight the proof would formalize:
  - Before time k: all traces look identical outside B (basin_masks)
  - At time k: m independent nodes outside B suddenly differ
  - The only graph-theoretically consistent explanation: a node inside
    or at ∂B changed state, and its edges route to all m outcome nodes.
  - With enough m (relative to |∂B|), this gateway is uniquely forced.

  This is abductive inference made into a theorem:
  NOT "correlation implies causation"
  BUT "sufficient independent correlated escapes imply gateway existence"

  Next steps to close the sorry:
  1. Define basin_boundary : Finset Node (nodes in B with edges outside B)
  2. Show each escape src must lie in basin_boundary (from basin_masks)
  3. Apply Finset.exists_ne_map_eq_of_card_lt (pigeonhole) to force
     a common gateway when m > |basin_boundary|
  4. Show that common gateway routes to all outcomes in one trace.
-/
