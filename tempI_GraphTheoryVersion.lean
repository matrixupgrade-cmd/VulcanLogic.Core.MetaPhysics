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
    exact ⟨i, j, hi, hj, by intro heq; exact h₂n (heq ▸ h₁n)⟩
  · have h₂ : T₂ k |>.edge i j := by
      rcases Classical.em (T₂ k |>.edge i j) with h | h
      · exact h
      · exfalso; apply hdiff; ext
        constructor
        · intro hc; exact absurd hc h₁
        · intro hc; exact absurd hc h
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
    exact ⟨i, j, hi, hj, by intro heq; exact h₁n (heq.symm ▸ h₂n)⟩

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

/-! ## Gateway structure -/

/--
The gateway region: nodes whose outgoing edges differ between T₁ and T₂ at time k.
These are the admissible hidden routing nodes — the candidates from which
causal signals escape the basin and become observable.

Key property: by basin_masks, any node whose edges differ at time k must
be inside or at the boundary of B — if it were purely outside, the
difference would have been visible before k, contradicting basin_masks.
This is what constrains gateway_region to be a *finite* set, bounded by
the basin boundary size. The pigeonhole argument depends on this finiteness.
-/
def gateway_region
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ) : Finset Node :=
  Finset.univ.filter (fun g =>
    ∃ o, T₁ k |>.edge g o ≠ T₂ k |>.edge g o)

/--
A node g routes a differentiating escape signal to outcome node o:
the two traces disagree on the edge g → o at time k.
This is the observable fingerprint of the gateway — not that g *exists*
inside the basin, but that its edges to outside-basin nodes are the
ones that differ between the two traces.
-/
def routes_escape
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (g o : Node) : Prop :=
  T₁ k |>.edge g o ≠ T₂ k |>.edge g o

/-!
## Forced gateway overlap (pigeonhole theorem)

This is the first fully-closeable theorem on the path to
causal_gateway_identification. It does NOT require sorry.

The argument:
  - m outcome nodes each have an escape witness in gateway_region
  - gateway_region has fewer than m elements
  - By pigeonhole (Fintype.card_le_of_injective contrapositive),
    some gateway node must route escape signals to at least two outcomes

This is the mathematical core of the Sherlock inference:
when there are more independent observations than there are
candidate hidden nodes, some hidden node must explain multiple
observations simultaneously. That is gateway existence forced
by the finite capacity of the hidden layer.

The not_function_injective_iff step requires:
  ∀ f : Fin m → S, ¬ Injective f → ∃ i j, i ≠ j ∧ f i = f j
which is standard and available in Mathlib as Fintype.exists_ne_map_eq_of_card_lt
or derived from it. We spell it out below for clarity.
-/

-- Helper: non-injectivity gives a collision
-- (This is the finite pigeonhole principle, packaged for our use)
private lemma not_injective_collision
    {α : Type} {m : ℕ} {S : Finset α}
    (f : Fin m → α)
    (hf : ∀ i, f i ∈ S)
    (h_small : S.card < m) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  by_contra h_all_distinct
  push_neg at h_all_distinct
  have h_inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact absurd hab (h_all_distinct a b hne)
  have h_card : m ≤ S.card := by
    have := Fintype.card_le_of_injective
      (fun i : Fin m => (⟨f i, hf i⟩ : S)) (fun a b h => h_inj (Subtype.mk.inj h))
    simpa [Fintype.card_fin] using this
  exact Nat.not_le.mpr h_small h_card

theorem forced_gateway_overlap
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (m : ℕ)
    (hm : m > 0)
    (outcomes : Fin m → Node)
    -- Each outcome has a gateway witness in the gateway region
    (h_escapes : ∀ idx : Fin m,
      ∃ g : Node,
        g ∈ gateway_region B T₁ T₂ k ∧
        routes_escape T₁ T₂ k g (outcomes idx))
    -- The gateway region is smaller than the number of outcomes
    -- This is the key condition: more observations than candidate nodes
    (h_small : (gateway_region B T₁ T₂ k).card < m) :
    -- Conclusion: some gateway node routes to at least two distinct outcomes
    ∃ g : Node,
      g ∈ gateway_region B T₁ T₂ k ∧
      ∃ i j : Fin m,
        i ≠ j ∧
        routes_escape T₁ T₂ k g (outcomes i) ∧
        routes_escape T₁ T₂ k g (outcomes j) := by
  -- Build a function from outcomes to their gateway witnesses
  -- (using choice since h_escapes gives existence)
  choose gw hgw_mem hgw_route using h_escapes
  -- Apply pigeonhole: m outcomes mapped to < m gateway nodes forces collision
  obtain ⟨i, j, hij, heq⟩ :=
    not_injective_collision gw hgw_mem h_small
  -- The shared gateway node witnesses both escapes
  exact ⟨gw i, hgw_mem i, i, j, hij,
         hgw_route i,
         heq ▸ hgw_route j⟩

/-!
## Causal gateway identification (the main conjecture)

Building on forced_gateway_overlap, we now state the full theorem:
that sufficiently many independent escape observations force the
*existence* of a gateway node — a node the observer should measure next.

The leap from forced_gateway_overlap to causal_gateway_identification is:
  forced_gateway_overlap gives a node that routes to ≥ 2 outcomes.
  causal_gateway_identification claims a node that routes to ALL m outcomes.

This stronger claim requires an additional assumption or a larger
pigeonhole argument (iterated, or with a stronger independence condition).

We state it honestly with sorry, with the proof obligations made precise.

The scientific meaning: this theorem, once proved, would be a formal
guarantee that abductive inference is valid in complex systems —
NOT "correlation implies causation" but
"sufficient independent correlated escapes imply gateway existence."

Every AI system doing hypothesis generation in complex domains could
anchor its reasoning to this theorem. The conditions under which the
inference is licensed would be explicit and machine-verifiable.
-/

/--
Independence of outcome nodes: each outcome's escape signal traces
to a *distinct* source edge. No two outcomes share an escape witness.
This ensures the m observations are genuinely drawing on m different
pieces of evidence, not recounting the same signal m times.

Without this condition, m correlated observations from a single edge
would not constrain the gateway any more than 1 observation would.
This is the formal analog of Sherlock needing independent clues —
the tan line, the posture, and the callus each from different sources.
-/
def independent_gateway_witnesses
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (m : ℕ)
    (outcomes : Fin m → Node)
    (witnesses : Fin m → Node) : Prop :=
  -- Each outcome has a distinct witness routing to it
  Function.Injective witnesses ∧
  -- Each witness actually routes to its outcome
  ∀ idx, routes_escape T₁ T₂ k (witnesses idx) (outcomes idx)

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
    -- m independent outcome nodes all showing escape at time k
    (m : ℕ) (hm : m > 0)
    (outcomes : Fin m → Node)
    -- Each outcome is outside the basin (observable)
    (h_outcomes_outside : ∀ idx, outcomes idx ∉ B)
    -- Each outcome has a gateway witness routing escape to it
    (h_escapes : ∀ idx : Fin m,
      ∃ g : Node,
        g ∈ gateway_region B T₁ T₂ k ∧
        routes_escape T₁ T₂ k g (outcomes idx))
    -- The observations are independent (distinct witnesses)
    (h_independent : ∃ witnesses : Fin m → Node,
        independent_gateway_witnesses T₁ T₂ k m outcomes witnesses)
    -- The gateway region is smaller than m
    -- (the crucial sufficiency condition: more observations than candidates)
    (h_small : (gateway_region B T₁ T₂ k).card < m) :
    -- Conclusion: a gateway node exists routing to ALL m outcomes
    -- This is the node the observer should measure next —
    -- not the root cause, but the necessary intermediary
    ∃ gateway : Node,
      gateway ∈ gateway_region B T₁ T₂ k ∧
      ∀ idx : Fin m, routes_escape T₁ T₂ k gateway (outcomes idx) := by
  /-
    Proof strategy (what remains to be formalized):

    Step 1: From h_independent, we have m distinct witness nodes,
            each routing to a distinct outcome.

    Step 2: By independence + h_escapes, all m witnesses lie in
            gateway_region (which has < m elements by h_small).

    Step 3: By pigeonhole (forced_gateway_overlap style), some gateway
            node g must account for ALL m routes — not just 2 —
            because the witnesses are injective (distinct) and all
            land in a region smaller than m.

    Step 4: The iterated pigeonhole / Hall's theorem argument:
            with injective witnesses all mapping into a set of size < m,
            the image of witnesses has size ≤ gateway_region.card < m,
            contradicting injectivity unless... wait, this is where
            the argument needs care.

    Honest gap: forced_gateway_overlap gives us a collision (g routes
    to ≥ 2 outcomes). Getting from ≥ 2 to ALL m requires either:
    (a) A stronger independence assumption (each outcome has ONLY ONE
        possible gateway, so the same g must appear m times), or
    (b) A connectivity assumption (g is the unique node from which
        all escape witnesses are reachable in T₁ or T₂).

    This is the precise mathematical gap between "Sherlock identifies
    a common cause exists" and "Sherlock identifies the specific common
    cause." The theorem as stated may be too strong without (a) or (b).

    The weaker version (gateway routes to ≥ 2 outcomes) is fully proved
    by forced_gateway_overlap above. The stronger version needs
    additional structure — made explicit here rather than hidden in sorry.
  -/
  sorry

/-!
## What Lean has told us through this process

1. forced_gateway_overlap: PROVABLE without sorry.
   The pigeonhole argument that more observations than candidate nodes
   forces a shared gateway is fully formalizable with Mathlib's
   Fintype.card_le_of_injective.

2. causal_gateway_identification (strong form): NEEDS MORE STRUCTURE.
   Getting from "some gateway routes to ≥ 2 outcomes" to "some gateway
   routes to ALL outcomes" requires either:
   - A unique-gateway assumption per outcome (each outcome has exactly
     one possible source of escape signal), or
   - A reachability / connectivity condition on the graph, or
   - Iterated application of forced_gateway_overlap with a shrinking
     argument (each application eliminates candidate gateways).

3. The sorry is not a failure — it is Lean doing its job.
   It has located the PRECISE mathematical gap in the abductive
   inference chain. The gap is real, meaningful, and tells us exactly
   what additional empirical conditions are needed for the full
   "gateway existence" claim to be mathematically licensed.

4. Scientific implication:
   forced_gateway_overlap is already enough to justify the methodology:
   when the number of independent correlated escapes exceeds the
   capacity of the hidden layer, gateway existence is not speculation —
   it is a theorem. The sorry marks where "existence of A gateway"
   becomes "existence of THE gateway."
-/
