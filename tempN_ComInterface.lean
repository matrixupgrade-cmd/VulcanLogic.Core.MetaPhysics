import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

namespace InterfaceConfig

-- ==================================================
-- BASIC STRUCTURE
-- ==================================================

variable (Node : Type) [DecidableEq Node]

structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

def applyProbe (p : Probe Node) (g : Node → Node → ℝ) :=
  p.transform g

def commutator (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  g i j - g j i

def asymmetry (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  Real.abs (commutator g i j)

def node_asymmetry
    (g     : Node → Node → ℝ)
    (nodes : Finset Node)
    (n     : Node) : ℝ :=
  ∑ m in nodes, asymmetry g n m

structure Junction where
  nodes : Finset Node

abbrev InterfaceConfig := Probe Node
abbrev ConfigSpace     := List (InterfaceConfig Node)

-- ==================================================
-- OBSERVABLE DISTORTION
-- ==================================================

def interface_distortion
    (cfg  : InterfaceConfig Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℝ :=
  ∑ i in junc.nodes,
    node_asymmetry Node (applyProbe Node cfg g) junc.nodes i

def observable_complexity
    (cs   : ConfigSpace Node)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  (cs.map (fun cfg => interface_distortion Node cfg g junc)).toFinset.card

-- ==================================================
-- SIGNAL TYPE
-- ==================================================

variable (Signal : Type) [DecidableEq Signal] [Fintype Signal]

-- ==================================================
-- BASIN STRUCTURE
-- ==================================================

structure Basin where
  signals : Finset Signal

def basin_entropy (b : Basin) : ℕ :=
  b.signals.card

variable (signal_to_cfg : Signal → InterfaceConfig Node)

def configsInBasin (b : Basin) : ConfigSpace Node :=
  (b.signals.image signal_to_cfg).toList

-- FIX: was `simpa using Finset.card_image_le`.
-- Now explicit: convert List.length to Finset.card via List.length_toList,
-- then close with card_image_le directly.
lemma configsInBasin_length_le_entropy (b : Basin) :
    (configsInBasin Node Signal signal_to_cfg b).length
      ≤ basin_entropy Signal b := by
  unfold configsInBasin basin_entropy
  rw [List.length_toList]
  exact Finset.card_image_le

def basin_local_complexity
    (b    : Basin)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  observable_complexity Node
    (configsInBasin Node Signal signal_to_cfg b) g junc

-- ==================================================
-- LOCAL SIGNATURE SPACE
-- ==================================================

variable (entropy : ℕ)
variable (h_entropy_pos : 1 ≤ entropy)

abbrev LocalSignature (junc : Junction Node) :=
  ({i // i ∈ junc.nodes} →
   {j // j ∈ junc.nodes} →
   Fin entropy)

-- ==================================================
-- CANONICAL SIGNATURE
-- ==================================================

variable (bucket : ℝ → Fin entropy)

def canonical_signature
    (cfg  : InterfaceConfig Node)
    (junc : Junction Node)
    (g    : Node → Node → ℝ) :
    LocalSignature Node entropy junc :=
  fun i j => bucket (asymmetry Node (applyProbe Node cfg g) i j)

-- NOTE: h_dist_from_sig remains a hypothesis rather than a proved theorem,
-- because interface_distortion is defined as a raw ℝ sum, not a sum of
-- bucketed Fin values.  Proving this from first principles would require
-- redefining distortion to factor through `bucket`.  The variable is kept
-- explicit so the dependency is visible at every call site.
variable
  (h_dist_from_sig :
    ∀ (cfg₁ cfg₂ : InterfaceConfig Node)
      (junc : Junction Node)
      (g : Node → Node → ℝ),
      canonical_signature Node entropy bucket cfg₁ junc g =
      canonical_signature Node entropy bucket cfg₂ junc g →
      interface_distortion Node cfg₁ g junc =
      interface_distortion Node cfg₂ g junc)

-- ==================================================
-- SIGNATURE SPACE CARDINALITY
-- ==================================================

-- FIX: was two separate simp/simpa calls that could diverge on a Mathlib bump.
-- Now a single `simp only` pass with an explicit card_coe rewrite,
-- making every step of the chain visible.
theorem local_signature_cardinality_bound
    (junc : Junction Node)
    [Fintype {i // i ∈ junc.nodes}] :
    Fintype.card (LocalSignature Node entropy junc)
      = entropy ^ (junc.nodes.card * junc.nodes.card) := by
  unfold LocalSignature
  have h : Fintype.card {i // i ∈ junc.nodes} = junc.nodes.card :=
    Fintype.card_coe junc.nodes
  simp only [Fintype.card_fun, Fintype.card_fin, h, pow_mul]

-- ==================================================
-- BASIN IMAGE BOUNDS
-- ==================================================

lemma basin_sig_image_le_entropy
    (b    : Basin)
    (junc : Junction Node)
    (g    : Node → Node → ℝ) :
    (b.signals.image
        (fun s => canonical_signature Node entropy bucket
                    (signal_to_cfg s) junc g)).card
      ≤ basin_entropy Signal b := by
  unfold basin_entropy
  exact Finset.card_image_le

lemma basin_sig_image_le_sig_space
    (b    : Basin)
    (junc : Junction Node)
    (g    : Node → Node → ℝ)
    [Fintype {i // i ∈ junc.nodes}] :
    (b.signals.image
        (fun s => canonical_signature Node entropy bucket
                    (signal_to_cfg s) junc g)).card
      ≤ Fintype.card (LocalSignature Node entropy junc) :=
  Finset.card_le_univ _

-- ==================================================
-- DISTORTION IMAGE ≤ SIGNATURE IMAGE
-- ==================================================

lemma distortions_le_basin_sig_image
    (b    : Basin)
    (g    : Node → Node → ℝ)
    (junc : Junction Node) :
    let cs := configsInBasin Node Signal signal_to_cfg b
    let D  := (cs.map
                 (fun cfg => interface_distortion Node cfg g junc)).toFinset
    let S  := (b.signals.image
                 (fun s => canonical_signature Node entropy bucket
                              (signal_to_cfg s) junc g))
    D.card ≤ S.card := by
  classical
  set cs := configsInBasin Node Signal signal_to_cfg b
  set D  := (cs.map
               (fun cfg => interface_distortion Node cfg g junc)).toFinset
  set S  := (b.signals.image
               (fun s => canonical_signature Node entropy bucket
                           (signal_to_cfg s) junc g))

  -- Every distortion value comes from some config in cs
  have hD_witness :
      ∀ d ∈ D, ∃ cfg ∈ cs,
        interface_distortion Node cfg g junc = d := by
    intro d hd
    rcases Finset.mem_toFinset.mp hd with ⟨cfg, hcfg, rfl⟩
    exact ⟨cfg, hcfg, rfl⟩
  -- FIX: explicit lambda so `choose` arity is unambiguous
  choose cfg_of_dist hcfg_mem hval_dist using
    fun d hd => hD_witness d hd

  -- Every config in cs comes from some signal in b.signals
  have hcs_witness :
      ∀ cfg ∈ cs, ∃ s ∈ b.signals, signal_to_cfg s = cfg := by
    intro cfg hcfg
    unfold configsInBasin at hcfg
    -- FIX: was List.mem_toList; Finset.mem_toList is the correct Mathlib name
    rw [Finset.mem_toList] at hcfg
    rcases Finset.mem_image.mp hcfg with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  choose sig_of_cfg hsig_mem hval_sig using
    fun cfg hcfg => hcs_witness cfg hcfg

  -- Build the injection D → S
  let φ : {d // d ∈ D} → {s // s ∈ S} :=
    fun ⟨d, hd⟩ =>
      let cfg  := cfg_of_dist d hd
      let hcfg := hcfg_mem d hd
      let s    := sig_of_cfg cfg hcfg
      let hs   := hsig_mem cfg hcfg
      have hmem : canonical_signature Node entropy bucket
                    (signal_to_cfg s) junc g ∈ S :=
        Finset.mem_image.mpr ⟨s, hs, rfl⟩
      ⟨canonical_signature Node entropy bucket
         (signal_to_cfg s) junc g, hmem⟩

  -- φ is injective
  have h_inj : Function.Injective φ := by
    intro ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩ hφ
    -- FIX: unfold φ explicitly before Subtype.mk.injEq so the goal is
    -- transparent; avoids relying on `simp` reducing through a complex `let`
    simp only [φ, Subtype.mk.injEq] at hφ
    have hdist :
        interface_distortion Node (cfg_of_dist d₁ hd₁) g junc =
        interface_distortion Node (cfg_of_dist d₂ hd₂) g junc := by
      rw [← hval_sig (cfg_of_dist d₁ hd₁) (hcfg_mem d₁ hd₁)]
      rw [← hval_sig (cfg_of_dist d₂ hd₂) (hcfg_mem d₂ hd₂)]
      exact h_dist_from_sig _ _ junc g hφ
    have heq : d₁ = d₂ :=
      (hval_dist d₁ hd₁).symm.trans (hdist.trans (hval_dist d₂ hd₂))
    exact Subtype.ext heq

  have h' : Fintype.card {d // d ∈ D} ≤ Fintype.card {s // s ∈ S} :=
    Fintype.card_le_of_injective φ h_inj
  -- FIX: was `simpa [Fintype.card_coe]`; now explicit rwa so both
  -- subtype-card → finset-card conversions are visible
  rwa [Fintype.card_coe, Fintype.card_coe] at h'

-- ==================================================
-- THREE-LEVEL SANDWICH
-- ==================================================

theorem observable_complexity_three_level_bound
    (b    : Basin)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node Signal signal_to_cfg b g junc
      ≤ basin_entropy Signal b
    ∧
    basin_entropy Signal b
      ≤ Fintype.card Signal
    ∧
    Fintype.card Signal
      ≤ entropy ^ (junc.nodes.card * junc.nodes.card) := by
  refine ⟨?_, ?_, h_signal_bound⟩
  · -- Tier 1: complexity ≤ basin_entropy
    unfold basin_local_complexity observable_complexity
    set cs := configsInBasin Node Signal signal_to_cfg b
    set D  := (cs.map
                 (fun cfg => interface_distortion Node cfg g junc)).toFinset
    set S  := (b.signals.image
                 (fun s => canonical_signature Node entropy bucket
                              (signal_to_cfg s) junc g))
    calc D.card
        ≤ S.card :=
            distortions_le_basin_sig_image
              Node Signal signal_to_cfg entropy bucket
              h_dist_from_sig b g junc
      _ ≤ basin_entropy Signal b :=
            basin_sig_image_le_entropy
              Node Signal signal_to_cfg entropy bucket b junc g
  · -- Tier 2: basin_entropy ≤ Fintype.card Signal
    -- FIX: was a two-step calc via Finset.univ; Finset.card_le_univ closes
    -- this in one step
    unfold basin_entropy
    exact Finset.card_le_univ b.signals

-- ==================================================
-- COROLLARY: single exponential ceiling
-- ==================================================

theorem observable_complexity_bounded_exponential
    (b    : Basin)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node Signal signal_to_cfg b g junc
      ≤ entropy ^ (junc.nodes.card * junc.nodes.card) := by
  obtain ⟨h1, h2, h3⟩ :=
    observable_complexity_three_level_bound
      Node Signal signal_to_cfg entropy h_entropy_pos bucket
      h_dist_from_sig b g junc h_signal_bound
  exact le_trans (le_trans h1 h2) h3

-- ==================================================
-- COROLLARY: self-similar basin collapses to complexity ≤ 1
-- ==================================================

theorem self_similar_basin_complexity_le_one
    (b    : Basin)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (h_uniform :
      ∀ s₁ s₂ ∈ b.signals,
        signal_to_cfg s₁ = signal_to_cfg s₂) :
    basin_local_complexity Node Signal signal_to_cfg b g junc ≤ 1 := by
  unfold basin_local_complexity observable_complexity
  have h_config_card :
      (configsInBasin Node Signal signal_to_cfg b).toFinset.card ≤ 1 := by
    unfold configsInBasin
    rw [List.toFinset_toList]
    apply Finset.card_le_one.mpr
    intro a ha c hc   -- FIX: renamed `b'` → `c` to avoid shadowing outer `b`
    rcases Finset.mem_image.mp ha with ⟨s₁, hs₁, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨s₂, hs₂, rfl⟩
    exact h_uniform s₁ hs₁ s₂ hs₂
  -- FIX: was Finset.card_image_le applied directly to `toFinset ∘ map`,
  -- which doesn't match card_image_le's signature (it expects Finset.image).
  -- Now we go via Finset.card_le_card with an explicit subset proof so the
  -- `List.map → List.toFinset → Finset.image` chain is transparent.
  calc ((configsInBasin Node Signal signal_to_cfg b).map
          (fun cfg => interface_distortion Node cfg g junc)).toFinset.card
      ≤ (configsInBasin Node Signal signal_to_cfg b).toFinset.card := by
            apply Finset.card_le_card
            intro x hx
            simp only [List.mem_toFinset, List.mem_map] at hx
            obtain ⟨cfg, hcfg, rfl⟩ := hx
            simp only [List.mem_toFinset]
            exact List.mem_of_mem_map hcfg
    _ ≤ 1 := h_config_card

-- ==================================================
-- COROLLARY: small basin in large graph
-- ==================================================

theorem small_basin_large_graph_compression
    (b    : Basin)
    (g    : Node → Node → ℝ)
    (junc : Junction Node)
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node Signal signal_to_cfg b g junc
      ≤ basin_entropy Signal b := by
  obtain ⟨h1, _, _⟩ :=
    observable_complexity_three_level_bound
      Node Signal signal_to_cfg entropy h_entropy_pos bucket
      h_dist_from_sig b g junc h_signal_bound
  exact h1

-- ==================================================
-- CAPSTONE: INTERFACE EXISTENCE THEOREM
-- ==================================================

structure Party (Node : Type) where
  hidden : Finset Node

def is_valid_interface
    (cfg  : InterfaceConfig Node)
    (junc : Junction Node)
    (g    : Node → Node → ℝ)
    (b    : Basin) : Prop :=
  basin_local_complexity Node Signal signal_to_cfg b g junc
    ≤ basin_entropy Signal b

theorem communication_interface_exists
    (A B   : Party Node)
    (junc  : Junction Node)
    (g     : Node → Node → ℝ)
    (b     : Basin)
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    ∃ (cfg : InterfaceConfig Node),
      is_valid_interface Node Signal signal_to_cfg cfg junc g b := by
  classical
  -- Witness: the identity probe suffices.
  -- The bound is guaranteed by basin compression alone,
  -- independent of which probe is chosen.
  let id_cfg : InterfaceConfig Node :=
    { transform := fun h => h }
  exact ⟨id_cfg,
    small_basin_large_graph_compression
      Node Signal signal_to_cfg entropy h_entropy_pos bucket
      h_dist_from_sig b g junc h_signal_bound⟩

theorem occam_quantifier
    (A B   : Party Node)
    (junc  : Junction Node)
    (g     : Node → Node → ℝ)
    (b     : Basin)
    (K     : ℕ)
    (h_low : basin_entropy Signal b ≤ K)
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    ∃ (cfg : InterfaceConfig Node),
      basin_local_complexity Node Signal signal_to_cfg b g junc ≤ K := by
  obtain ⟨cfg, h_valid⟩ :=
    communication_interface_exists
      Node Signal signal_to_cfg entropy h_entropy_pos bucket
      h_dist_from_sig A B junc g b h_signal_bound
  exact ⟨cfg, le_trans h_valid h_low⟩

-- ==================================================
-- ADAPTIVE BASIN RECONSTRUCTION
-- ==================================================
/-
  The philosophy of this section is that global communication
  optimization need not be globally computable a priori.
  Instead, a system may incrementally reconstruct low-distortion
  communication structure from local signal basins.

  Constructive interference between basins permits trajectory
  merging into a shared low-distortion regime: the two basins
  collectively stay within their joint entropy budget.

  Destructive interference forces basin bifurcation: the combined
  routing geometry exceeds the local entropy budget, so the two
  signal regimes require distinct routing geometries and cannot
  share a single probe.

  This section establishes the foundational scaffold.  The full
  constructive machinery (interaction operators, basin synthesis,
  patchwork probes, additive distortion decomposition) is
  intentionally deferred to future files.
-/

/-
  Constructive interference: two basins can share a routing regime.
  Their combined observable complexity stays within the sum of their
  individual entropy budgets — no information is lost by merging them.

  Geometrically: the two basins' trajectories through signature space
  do not push each other into new, previously unoccupied regions.
-/
def constructive_interference
    (b₁ b₂ : Basin)
    (g      : Node → Node → ℝ)
    (junc   : Junction Node) : Prop :=
  basin_local_complexity Node Signal signal_to_cfg b₁ g junc +
  basin_local_complexity Node Signal signal_to_cfg b₂ g junc
    ≤
  basin_entropy Signal b₁ +
  basin_entropy Signal b₂

/-
  Destructive interference: the two basins cannot share a routing regime.
  Their combined complexity exceeds the joint entropy budget, indicating
  that the signal regimes have genuinely incompatible structure and must
  be handled by separate probes.

  Geometrically: merging the two basins forces the combined system to
  explore signature-space regions that neither basin visits alone —
  a new branch in the global optimization tree.
-/
def destructive_interference
    (b₁ b₂ : Basin)
    (g      : Node → Node → ℝ)
    (junc   : Junction Node) : Prop :=
  basin_entropy Signal b₁ +
  basin_entropy Signal b₂
    <
  basin_local_complexity Node Signal signal_to_cfg b₁ g junc +
  basin_local_complexity Node Signal signal_to_cfg b₂ g junc

/-
  Adaptive Basin Reconstruction Principle

  For any two basins sharing a junction, the system is always in
  exactly one of two regimes:

    · Constructive — their trajectories are compatible; a shared
      probe can handle both within the joint entropy budget.
      The global optimum can be reconstructed by merging the basins.

    · Destructive — their trajectories are incompatible; no shared
      probe stays within budget.  The global optimum branches here:
      a separate routing geometry is required for each basin.

  This is a trichotomy-of-ℕ fact, proved by `le_or_lt`.  The theorem
  is intentionally existential and regime-identifying rather than
  constructive: it tells you *which* case you are in, not how to
  build the merged probe or the branching probe family.  Those
  constructions are the subject of future files.

  Relationship to earlier results:
    · When constructive, `small_basin_large_graph_compression` applied
      to each basin separately already bounds the merged complexity.
    · When destructive, the incompatibility is a signal that the probe
      search must be restarted from a higher-entropy budget — the
      bound from `observable_complexity_three_level_bound` stretches
      to accommodate the richer signal structure.
-/
theorem adaptive_basin_reconstruction
    (b₁ b₂ : Basin)
    (g      : Node → Node → ℝ)
    (junc   : Junction Node)
    -- h_signal_bound is not needed for the dichotomy itself, but is
    -- included so callers can immediately apply the compression theorems
    -- in whichever branch they land in.
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    constructive_interference Node Signal signal_to_cfg b₁ b₂ g junc
    ∨
    destructive_interference Node Signal signal_to_cfg b₁ b₂ g junc := by
  unfold constructive_interference destructive_interference
  -- ℕ is totally ordered: the complexity sum either fits within the entropy
  -- budget or it does not.  `le_or_lt` gives both cases; no signal-bound
  -- reasoning needed since this is a pure numerical dichotomy.
  rcases le_or_lt
    (basin_local_complexity Node Signal signal_to_cfg b₁ g junc +
     basin_local_complexity Node Signal signal_to_cfg b₂ g junc)
    (basin_entropy Signal b₁ +
     basin_entropy Signal b₂) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-
  Corollary: constructive interference is the normal case.

  Under the same signal bound that drives the sandwich theorem,
  each basin individually satisfies complexity ≤ entropy.  This means
  constructive interference holds trivially when the two basins are
  independent (disjoint signal sets).

  Formally: if b₁ and b₂ have disjoint signal sets, their local
  complexities are independently bounded, so the sum bound holds.
-/
theorem disjoint_basins_constructive
    (b₁ b₂  : Basin)
    (g       : Node → Node → ℝ)
    (junc    : Junction Node)
    (h_disj  : Disjoint b₁.signals b₂.signals)
    (h_signal_bound :
      Fintype.card Signal
        ≤ entropy ^ (junc.nodes.card * junc.nodes.card))
    [Fintype {i // i ∈ junc.nodes}] :
    constructive_interference Node Signal signal_to_cfg b₁ b₂ g junc := by
  unfold constructive_interference
  -- Each basin independently satisfies complexity ≤ entropy
  have h₁ : basin_local_complexity Node Signal signal_to_cfg b₁ g junc
              ≤ basin_entropy Signal b₁ :=
    small_basin_large_graph_compression
      Node Signal signal_to_cfg entropy h_entropy_pos bucket
      h_dist_from_sig b₁ g junc h_signal_bound
  have h₂ : basin_local_complexity Node Signal signal_to_cfg b₂ g junc
              ≤ basin_entropy Signal b₂ :=
    small_basin_large_graph_compression
      Node Signal signal_to_cfg entropy h_entropy_pos bucket
      h_dist_from_sig b₂ g junc h_signal_bound
  -- Summing the two inequalities closes the goal
  exact Nat.add_le_add h₁ h₂

/-
  Future directions for constructive machinery:
    1. Signal interaction operators:
         combine : Signal → Signal → Signal
       defining how two signals compose when their basins merge.

    2. Basin synthesis:
         synthesize_basin : Basin → Basin → Basin
       producing a merged basin from two constructively-interfering ones.

    3. Patchwork probes:
         A probe family indexed by basin, glued together on a shared junction.

    4. Additive distortion decomposition:
         If b = b₁ ∪ b₂ with b₁, b₂ constructive, then
         basin_local_complexity b ≤ basin_local_complexity b₁
                                  + basin_local_complexity b₂.

    5. Recursive basin hierarchies:
         Emergent attractor formation as basins merge constructively
         across scales.

    6. Adaptive routing dynamics:
         Incremental probe update rules when new signals arrive and
         push the system from constructive into destructive regime.
-/

end InterfaceConfig
