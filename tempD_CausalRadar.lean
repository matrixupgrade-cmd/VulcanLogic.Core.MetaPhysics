import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Hidden Routing Interface Dynamics

This file formalizes a framework for observer-limited causal systems.

Core philosophy:
- Observers do NOT reconstruct the full hidden graph.
- Observers only access projected return signals.
- Persistent timing asymmetries constrain the class of compatible
  hidden causal structures.

The framework avoids assuming:
- exact shortest paths,
- full graph observability,
- deterministic routing,
- probabilistic priors,
- explicit bypass structures.

Instead we reason about:
- hidden routing interfaces,
- observable timing geometry,
- persistence across traces,
- stable interval separation,
- gateway overlap inevitability.

Main conceptual theorem direction:

"In a sufficiently coupled finite causal system,
 persistent return-time outliers stable across monotone traces imply
 structurally distinct hidden routing interfaces."
-/

set_option autoImplicit false
open Finset Classical BigOperators

universe u

/-- Basic graph edge relation -/
abbrev Edge (Node : Type) := Node → Node → Prop

/-- Hidden causal graph -/
structure Graph (Node : Type) where
  edge : Edge Node

/-- Temporal evolution of hidden graphs -/
abbrev GraphTrace (Node : Type) := ℕ → Graph Node

/-- Observer-hidden basin region -/
abbrev Basin (Node : Type) := Finset Node

/-- Observable projection removing hidden basin structure -/
def project_graph
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (G : Graph Node) : Graph Node :=
{
  edge := fun i j =>
    i ∉ B ∧
    j ∉ B ∧
    G.edge i j
}

/-- Observer equivalence under hidden basin projection -/
def obs_equiv
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (G₁ G₂ : Graph Node) : Prop :=
  project_graph B G₁ = project_graph B G₂

/-- Hidden structural difference outside observer basin -/
def hidden_difference
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (G₁ G₂ : Graph Node) : Prop :=
  ∀ i j,
    i ∉ B →
    j ∉ B →
    (G₁.edge i j ↔ G₂.edge i j)

/-- Observable escape from hidden equivalence -/
def basin_escape
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (G₁ G₂ : Graph Node) : Prop :=
  ∃ i j,
    i ∉ B ∧
    j ∉ B ∧
    G₁.edge i j ≠ G₂.edge i j

/-- Observable edge-distance outside basin -/
def observable_distance
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (G₁ G₂ : Graph Node) : ℕ :=
  ∑ i, ∑ j,
    if i ∉ B ∧
       j ∉ B ∧
       G₁.edge i j ≠ G₂.edge i j
    then 1 else 0

/-! ## Temporal Persistence -/

/-- Monotone traces preserve existing edges forward in time -/
def monotone_trace
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T : GraphTrace Node) : Prop :=
  ∀ n i j,
    T n |>.edge i j →
    T (n + 1) |>.edge i j

/-- Two traces remain observationally equivalent up to time k -/
def basin_masks
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ) : Prop :=
  ∀ n < k,
    obs_equiv B (T₁ n) (T₂ n)

/-! ## Gateway Regions -/

/--
Gateway region:
observable nodes participating in differing causal routing behavior.
-/
def gateway_region
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ) : Finset Node :=
  Finset.univ.filter (fun g =>
    ∃ o,
      T₁ k |>.edge g o ≠
      T₂ k |>.edge g o)

/-- Observable routing divergence -/
def routes_escape
    {Node : Type} [Fintype Node] [DecidableEq Node]
    (T₁ T₂ : GraphTrace Node)
    (k : ℕ)
    (g o : Node) : Prop :=
  T₁ k |>.edge g o ≠
  T₂ k |>.edge g o

/-! ## Pigeonhole Core -/

/--
Finite congestion principle:
too many observable outcomes through too few gateways
forces overlap.
-/
lemma not_injective_collision
    {α : Type}
    {m : ℕ}
    {S : Finset α}
    (f : Fin m → α)
    (hf : ∀ i, f i ∈ S)
    (hsmall : S.card < m) :
    ∃ i j : Fin m,
      i ≠ j ∧
      f i = f j := by
  by_contra h
  push_neg at h

  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact absurd hab (h a b hne)

  have hcard :
      m ≤ S.card := by
    have :=
      Fintype.card_le_of_injective
        (fun i : Fin m => ⟨f i, hf i⟩)
        (fun a b hab =>
          hinj (Subtype.mk.inj hab))
    simpa [Fintype.card_fin] using this

  exact Nat.not_le.mpr hsmall hcard

/--
Forced gateway overlap theorem:
finite routing pressure forces shared observable gateways.
-/
theorem forced_gateway_overlap
    {Node : Type}
    [Fintype Node]
    [DecidableEq Node]
    (B : Basin Node)
    (T₁ T₂ : GraphTrace Node)
    (k m : ℕ)
    (outcomes : Fin m → Node)
    (hesc : ∀ i, ∃ g,
      g ∈ gateway_region B T₁ T₂ k ∧
      routes_escape T₁ T₂ k g (outcomes i))
    (hsmall :
      (gateway_region B T₁ T₂ k).card < m) :
    ∃ g i j,
      i ≠ j ∧
      g ∈ gateway_region B T₁ T₂ k ∧
      routes_escape T₁ T₂ k g (outcomes i) ∧
      routes_escape T₁ T₂ k g (outcomes j) := by

  choose gw hgw using hesc

  obtain ⟨i, j, hij, heq⟩ :=
    not_injective_collision
      gw
      (by
        intro i
        exact (hgw i).1)
      hsmall

  exact ⟨
    gw i,
    i,
    j,
    hij,
    (hgw i).1,
    (hgw i).2,
    heq ▸ (hgw j).2
  ⟩

/-! ## Return-Time Geometry -/

/--
Observable return-time interval.

The observer does not know exact hidden routes,
only bounded return behavior.
-/
structure ReturnInterval where
  min_time : ℝ
  max_time : ℝ
  valid : min_time ≤ max_time

/--
Return signature assigned to observable nodes.
-/
def ReturnSignature
    (Node : Type) :=
  Node → ReturnInterval

/--
Scatter dominance:
node a consistently returns no slower than node b.
-/
def scatter_dominates
    {Node : Type}
    (R : ReturnSignature Node)
    (a b : Node) : Prop :=
  (R a).max_time ≤
  (R b).min_time

/--
Observable interval overlap.
-/
def overlaps
    {Node : Type}
    (R : ReturnSignature Node)
    (a b : Node) : Prop :=
  ¬ (
    (R a).max_time < (R b).min_time ∨
    (R b).max_time < (R a).min_time
  )

/--
Persistent timing outlier:
stable non-overlapping return geometry relative
to the main observable population.
-/
def persistent_outlier
    {Node : Type}
    [Fintype Node]
    [DecidableEq Node]
    (nodes : Finset Node)
    (R : ReturnSignature Node)
    (s : Node) : Prop :=
  ∀ t ∈ nodes,
    t ≠ s →
    ¬ overlaps R s t

/--
Structurally distinct hidden routing interface.

Interpretation:
persistent timing asymmetry implies the node
interfaces with hidden causal structure differently.
-/
def distinct_hidden_interface
    {Node : Type}
    (R : ReturnSignature Node)
    (a b : Node) : Prop :=
  ¬ overlaps R a b

/-! ## Conceptual Theorem Direction -/

/--
Conceptual theorem schema:

Persistent return-time outliers imply distinct
hidden routing interfaces.

This avoids claiming:
- exact hidden bypasses,
- shortest path uniqueness,
- full graph reconstruction.

Instead it concludes:
persistent observable asymmetry implies
non-equivalent hidden structural coupling.
-/
theorem persistent_outlier_implies_distinct_interface
    {Node : Type}
    [Fintype Node]
    [DecidableEq Node]
    (nodes : Finset Node)
    (R : ReturnSignature Node)
    (s t : Node)
    (hout :
      persistent_outlier nodes R s)
    (ht :
      t ∈ nodes)
    (hne :
      t ≠ s) :
    distinct_hidden_interface R s t := by

  unfold persistent_outlier at hout
  unfold distinct_hidden_interface
  exact hout t ht hne

/-!
## Interpretation

This framework supports:

- observer-limited causality,
- hidden routing interfaces,
- return-time geometry,
- persistent asymmetry detection,
- finite causal rigidity arguments.

The framework intentionally avoids:
- exact graph reconstruction,
- metric assumptions,
- probabilistic priors,
- explicit bypass ontologies.

Core direction:

Persistent stable return-time asymmetries across
observable traces constrain compatible hidden
causal structure.

The observer does not infer the exact hidden graph.

The observer infers:
"structurally distinct hidden routing interfaces."
-/
