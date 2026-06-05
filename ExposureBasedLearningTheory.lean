/-
  ============================================================
  ExposureBasedLearningTheory.lean
  Author: Sean Timothy
  ============================================================

  Unified record of theorems about exposure-based learning
  systems across four proof directions.

  ──────────────────────────────────────────────────────────
  FOUR DIRECTIONS
  ──────────────────────────────────────────────────────────

  DIRECTION A — TRANSLATION DICTIONARY  (§9–12)
    Formal equivalence between the graph language
    (PathFactors, ApproximateClarity, deviation counts) and
    the algebraic language (effective_diversity,
    adaptive_threshold, reachable sets).
    Faithful + Complete assignments yield a full biconditional.
    Proofs may be started in either language and translated.

  DIRECTION B — CONSTRUCTIVE INJECTION  (§13–16)
    Discharges the SeparationCertifiesClarity obligation
    deferred in CausalSignature.lean §9.  Chain:
      board activity ↔ faithful encoding ↔ deviation = 1
      fingerprint sym-diff ↔ deviation disagreement count
      persistence → agreement after inj_time
      disagreement count ≤ inj_time → ApproxClarity bound
    Conditional form: T ≥ inj_time × ε_inv.
    Unconditional form: sep_const ≥ 1.

  DIRECTION C — COMPOUNDING  (§17–20)
    When blocking is resolved, rate is viable, and diversity
    exceeds one, learning compounds exponentially.
    Three tiers:
      Tier 1 — linear gap (no density condition)
      Tier 2 — one-step multiplier (1 + m) from density
      Tier 3 — iterated multiplier (1 + m)^k, exponential
    Capstone: any target threshold reachable in finite cycles.

  FOUNDATION — ALGEBRAIC WORLD  (§1–8)
    Core types, adaptive threshold, blocking trap, rate
    viability, infrastructure threshold, diversity mechanisms.

  ──────────────────────────────────────────────────────────
  GRAND SYNTHESIS  (§21)
    graph persistence → constructive injection → clarity
    → translation → algebraic diversity ≥ 2
    → combined rate > blocked rate → compounding
    → any target reachable in finite cycles.
  ──────────────────────────────────────────────────────────
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Tactic

universe u


-- ============================================================
-- 1. CORE TYPES
-- ============================================================

structure Basin where
  name : String
  deriving DecidableEq, BEq

structure Agent where
  exposure_count : ℕ
  memory         : Finset Basin
  utility        : ℝ
  cost           : ℝ


-- ============================================================
-- 2. THRESHOLD MODEL
-- ============================================================

/-
  Two-axis threshold:
    exposure axis  − 0.1 per observation
    diversity axis − 0.05 per basin in memory  (naive count; see §3 for correction)
-/
def adaptive_threshold (A : Agent) : ℝ :=
  3.0 - A.exposure_count.to_real * 0.1
      - A.memory.card.to_real      * 0.05

variable (observed_impact : Agent → Basin → ℝ)
variable (adoption_cost   : Agent → Basin → ℝ)

def net_gain (A : Agent) (B : Basin) : ℝ :=
  observed_impact A B - adoption_cost A B

def should_adopt (A : Agent) (B : Basin) : Prop :=
  net_gain observed_impact adoption_cost A B > adaptive_threshold A


-- ============================================================
-- 3. CAUSAL BRANCH ABSTRACTION
-- ============================================================

variable {BranchId : Type*} [DecidableEq BranchId]

/-- Effective diversity: cardinality of the branch image of memory. -/
def effective_diversity (branch_of : Basin → BranchId) (A : Agent) : ℕ :=
  (A.memory.image branch_of).card

theorem effective_le_memory (branch_of : Basin → BranchId) (A : Agent) :
    effective_diversity branch_of A ≤ A.memory.card :=
  Finset.card_image_le

/-- True threshold: uses effective_diversity rather than raw memory.card. -/
def true_threshold (branch_of : Basin → BranchId) (A : Agent) : ℝ :=
  3.0 - A.exposure_count.to_real                 * 0.1
      - (effective_diversity branch_of A).to_real * 0.05

/-- adaptive_threshold ≤ true_threshold; gap = (memory.card − effective_diversity) × 0.05. -/
theorem naive_threshold_leq_true (branch_of : Basin → BranchId) (A : Agent) :
    adaptive_threshold A ≤ true_threshold branch_of A := by
  unfold adaptive_threshold true_threshold
  have h : (effective_diversity branch_of A).to_real ≤ A.memory.card.to_real :=
    Nat.cast_le.mpr (effective_le_memory branch_of A)
  nlinarith

/-- Single-branch memory caps effective diversity at 1. -/
theorem single_branch_caps_diversity
    (branch_of : Basin → BranchId) (A : Agent) (b : BranchId)
    (h : ∀ B ∈ A.memory, branch_of B = b) :
    effective_diversity branch_of A ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [effective_diversity, Finset.mem_image] at hx hy
  obtain ⟨Bx, hBx, rfl⟩ := hx
  obtain ⟨By, hBy, rfl⟩ := hy
  rw [h Bx hBx, h By hBy]


-- ============================================================
-- 4. BLOCKING TRAP
-- ============================================================

theorem blocking_bounds_adoptability (A : Agent)
    (reachable : Finset Basin) (block_fidelity : ℝ)
    (h_bounded    : ∀ B ∈ reachable, observed_impact A B ≤ block_fidelity)
    (h_cost_nn    : ∀ B ∈ reachable, adoption_cost A B ≥ 0)
    (h_infeasible : block_fidelity ≤ adaptive_threshold A) :
    ∀ B ∈ reachable, ¬ should_adopt observed_impact adoption_cost A B := by
  intro B hB; unfold should_adopt net_gain; push_neg
  linarith [h_bounded B hB, h_cost_nn B hB]

/-- A trajectory confined to a fixed reachable set never reaches a
    basin outside it.  Algebraic dual of collective_clarity_blocked
    in CausalSignature.lean.
    Note: the initial condition `trajectory 0 = A₀` anchors the
    intended reading (A₀ is the blocked agent) but is not used in
    the proof — any trajectory confined to `reachable` traps
    `high_value` regardless of its starting point. -/
theorem blocking_trap
    (A₀ : Agent) (reachable : Finset Basin) (high_value : Basin)
    (h_unreachable : high_value ∉ reachable)
    (trajectory : ℕ → Agent)
    (_ : trajectory 0 = A₀)
    (h_restricted : ∀ n B, B ∈ (trajectory n).memory → B ∈ reachable) :
    ∀ n, high_value ∉ (trajectory n).memory := fun n h_in =>
  h_unreachable (h_restricted n high_value h_in)

theorem exposure_volume_does_not_escape_block
    (A₁ : Agent) (reachable : Finset Basin) (high_value : Basin)
    (h_unreachable : high_value ∉ reachable)
    (h_same_branch : ∀ B ∈ A₁.memory, B ∈ reachable) :
    high_value ∉ A₁.memory := fun h_in =>
  h_unreachable (h_same_branch high_value h_in)


-- ============================================================
-- 5. RATE VIABILITY THRESHOLD
-- ============================================================

noncomputable def per_step_net (r capacity vcr benefit : ℝ) : ℝ :=
  benefit - (if r > capacity then (r - capacity) * vcr else 0)

theorem rate_above_capacity_net_negative
    (r capacity vcr benefit : ℝ)
    (h_above : r > capacity) (h_dom : (r - capacity) * vcr > benefit) :
    per_step_net r capacity vcr benefit < 0 := by
  simp only [per_step_net, if_pos h_above]; linarith

theorem rate_within_capacity_beneficial
    (r capacity vcr benefit : ℝ)
    (h_within : r ≤ capacity) (h_benefit : benefit > 0) :
    per_step_net r capacity vcr benefit > 0 := by
  simp only [per_step_net, if_neg (not_lt.mpr h_within)]; linarith


-- ============================================================
-- 6. INFRASTRUCTURE THRESHOLD THEOREM
-- ============================================================

/-
  Same rate r is net-negative at capacity c_low and net-positive
  at capacity c_high.  The rate is fixed; the capacity changes.
-/
theorem infrastructure_converts_destructive_to_constructive
    (r c_low c_high vcr benefit : ℝ)
    (h_raise : r ≤ c_high) (h_below : r > c_low)
    (h_b_pos : benefit > 0) (h_pre_bad : (r - c_low) * vcr > benefit) :
    per_step_net r c_low  vcr benefit < 0 ∧
    per_step_net r c_high vcr benefit > 0 :=
  ⟨rate_above_capacity_net_negative r c_low  vcr benefit h_below  h_pre_bad,
   rate_within_capacity_beneficial  r c_high vcr benefit h_raise  h_b_pos⟩

theorem infrastructure_gap_has_positive_width
    (r vcr benefit : ℝ) (h_b_pos : benefit > 0) (h_vcr_pos : vcr > 0) :
    ∃ c_low c_high : ℝ,
        c_low < r ∧ r ≤ c_high ∧
        per_step_net r c_low  vcr benefit < 0 ∧
        per_step_net r c_high vcr benefit > 0 := by
  refine ⟨r - benefit / vcr - 1, r,
          by linarith [div_pos h_b_pos h_vcr_pos],
          le_refl r, ?_, ?_⟩
  · apply rate_above_capacity_net_negative
    · linarith [div_pos h_b_pos h_vcr_pos]
    · have key : r - (r - benefit / vcr - 1) = benefit / vcr + 1 := by ring
      rw [key]
      have hne  : vcr ≠ 0 := h_vcr_pos.ne'
      have hdiv : benefit / vcr * vcr = benefit := by rw [div_mul_cancel₀ _ hne]
      nlinarith
  · exact rate_within_capacity_beneficial r r vcr benefit (le_refl r) h_b_pos


-- ============================================================
-- 7. DIVERSITY ACCELERATION
-- ============================================================

theorem ai_window_nonempty
    (threshold c_trad c_ai : ℝ) (h_lower : c_ai < c_trad) :
    ∃ gain, gain > threshold + c_ai ∧ gain ≤ threshold + c_trad :=
  ⟨threshold + (c_trad + c_ai) / 2, by linarith, by linarith⟩

theorem ai_diversity_lowers_true_threshold
    (k : ℕ) (hk : k ≥ 2) (exp_base : ℝ)
    (ai_div blk_div : ℕ)
    (h_ai  : ai_div  = k) (h_blk : blk_div ≤ 1) :
    3.0 - exp_base - ai_div.to_real  * 0.05
    <
    3.0 - exp_base - blk_div.to_real * 0.05 := by
  have h1 : blk_div.to_real ≤ 1  := Nat.cast_le.mpr h_blk
  have h2 : ai_div.to_real  = ↑k := by exact_mod_cast h_ai
  have h3 : (k : ℝ) ≥ 2          := by exact_mod_cast hk
  linarith

theorem ai_economy_theorem
    (threshold c_trad c_ai : ℝ) (h_lower : c_ai < c_trad)
    (k : ℕ) (hk : k ≥ 2) (exp_base : ℝ)
    (ai_div blk_div : ℕ) (h_ai : ai_div = k) (h_blk : blk_div ≤ 1) :
    (∃ gain, gain > threshold + c_ai ∧ gain ≤ threshold + c_trad) ∧
    3.0 - exp_base - ai_div.to_real * 0.05
      < 3.0 - exp_base - blk_div.to_real * 0.05 :=
  ⟨ai_window_nonempty threshold c_trad c_ai h_lower,
   ai_diversity_lowers_true_threshold k hk exp_base ai_div blk_div h_ai h_blk⟩


-- ============================================================
-- 8. COMPOSITE: THREE INDEPENDENT MECHANISMS
-- ============================================================

theorem learning_economy_composite
    (A₀ : Agent) (reachable : Finset Basin) (high_value : Basin)
    (h_unreachable : high_value ∉ reachable)
    (r c_low c_high vcr benefit : ℝ)
    (h_raise : r ≤ c_high) (h_below : r > c_low)
    (h_b_pos : benefit > 0) (h_pre_bad : (r - c_low) * vcr > benefit)
    (threshold c_trad c_ai : ℝ) (h_ai_lower : c_ai < c_trad)
    (k : ℕ) (hk : k ≥ 2) (exp_base : ℝ)
    (ai_div blk_div : ℕ) (h_ai : ai_div = k) (h_blk : blk_div ≤ 1) :
    (∀ (traj : ℕ → Agent),
        traj 0 = A₀ →
        (∀ n B, B ∈ (traj n).memory → B ∈ reachable) →
        ∀ n, high_value ∉ (traj n).memory)
    ∧ (per_step_net r c_low  vcr benefit < 0 ∧
       per_step_net r c_high vcr benefit > 0)
    ∧ ((∃ gain, gain > threshold + c_ai ∧ gain ≤ threshold + c_trad) ∧
       3.0 - exp_base - ai_div.to_real * 0.05
         < 3.0 - exp_base - blk_div.to_real * 0.05) := by
  refine ⟨?_, ?_, ?_⟩
  · intro traj _ h_restricted n h_in
    exact h_unreachable (h_restricted n high_value h_in)
  · exact infrastructure_converts_destructive_to_constructive
        r c_low c_high vcr benefit h_raise h_below h_b_pos h_pre_bad
  · exact ai_economy_theorem threshold c_trad c_ai h_ai_lower
        k hk exp_base ai_div blk_div h_ai h_blk


-- ============================================================
-- 9. DIRECTION A: ABSTRACT PATH PREDICATE & ASSIGNMENT
-- ============================================================

/-
  PathPred src block obs:
    "obs receives src's signal only through block"
  Generalises PathFactors from CausalSignature.lean §16.
  NodeType is abstract; all translation theorems hold for any
  concrete graph (Fin 5, arbitrary DAG, etc.).
-/
variable {NodeType : Type*} [DecidableEq NodeType]

/-- Faithful: graph blocking implies same algebraic branch. -/
def Faithful
    (PathPred  : NodeType → NodeType → NodeType → Prop)
    (src       : NodeType)
    (n2b       : NodeType → Basin)
    (branch_of : Basin → BranchId) : Prop :=
  ∀ block obs : NodeType,
    PathPred src block obs →
    branch_of (n2b obs) = branch_of (n2b block)

/-- Complete: same algebraic branch implies graph blocking. -/
def Complete
    (PathPred  : NodeType → NodeType → NodeType → Prop)
    (src       : NodeType)
    (n2b       : NodeType → Basin)
    (branch_of : Basin → BranchId) : Prop :=
  ∀ block obs : NodeType,
    branch_of (n2b obs) = branch_of (n2b block) →
    PathPred src block obs

/-- IsomorphicAssignment: Faithful + Complete; full biconditional. -/
def IsomorphicAssignment
    (PathPred  : NodeType → NodeType → NodeType → Prop)
    (src       : NodeType)
    (n2b       : NodeType → Basin)
    (branch_of : Basin → BranchId) : Prop :=
  Faithful PathPred src n2b branch_of ∧
  Complete PathPred src n2b branch_of


-- ============================================================
-- 10. DIRECTION A: UTILITY LEMMAS
-- ============================================================

/-
  Function.Injective n2b is a load-bearing assumption for the trap
  theorems below and in §11.  Without injectivity, two distinct
  nodes can map to the same basin and the algebraic image loses the
  graph's structural information.  Every theorem that relies on
  node_not_in_S_gives_basin_not_in_image carries h_inj explicitly.
-/

lemma two_distinct_branches_ge_two
    (branch_of : Basin → BranchId) (A : Agent) (B₁ B₂ : Basin)
    (h₁ : B₁ ∈ A.memory) (h₂ : B₂ ∈ A.memory)
    (h_ne : branch_of B₁ ≠ branch_of B₂) :
    2 ≤ effective_diversity branch_of A := by
  unfold effective_diversity
  have hmem₁ : branch_of B₁ ∈ A.memory.image branch_of :=
    Finset.mem_image.mpr ⟨B₁, h₁, rfl⟩
  have hmem₂ : branch_of B₂ ∈ A.memory.image branch_of :=
    Finset.mem_image.mpr ⟨B₂, h₂, rfl⟩
  have h_lt : 1 < (A.memory.image branch_of).card :=
    Finset.one_lt_card.mpr ⟨_, hmem₁, _, hmem₂, h_ne⟩
  omega

lemma node_in_S_gives_basin_in_memory
    (n2b : NodeType → Basin) (S : Finset NodeType) (A : Agent)
    (h_mem : A.memory = S.image n2b) (obs : NodeType) (h_obs : obs ∈ S) :
    n2b obs ∈ A.memory := by
  rw [h_mem]; exact Finset.mem_image.mpr ⟨obs, h_obs, rfl⟩

lemma node_not_in_S_gives_basin_not_in_image
    (n2b : NodeType → Basin) (h_inj : Function.Injective n2b)
    (S : Finset NodeType) (target : NodeType) (h_out : target ∉ S) :
    n2b target ∉ S.image n2b := by
  intro h_in
  simp only [Finset.mem_image] at h_in
  obtain ⟨obs, h_obs, h_eq⟩ := h_in
  exact h_out (h_inj h_eq ▸ h_obs)


-- ============================================================
-- 11. DIRECTION A: GRAPH → ALGEBRAIC BRIDGES
-- ============================================================

/-- Graph blocking → diversity cap.
    collective_clarity_blocked ↦ single_branch_caps_diversity. -/
theorem graph_blocking_implies_diversity_cap
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block : NodeType) (S : Finset NodeType)
    (h_all : ∀ obs ∈ S, PathPred src block obs)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_faith : Faithful PathPred src n2b branch_of)
    (A : Agent) (h_mem : A.memory = S.image n2b) :
    effective_diversity branch_of A ≤ 1 := by
  apply single_branch_caps_diversity branch_of A (branch_of (n2b block))
  intro B hB; rw [h_mem] at hB
  simp only [Finset.mem_image] at hB
  obtain ⟨obs, h_obs, rfl⟩ := hB
  exact h_faith block obs (h_all obs h_obs)

/-- Graph independence → diversity ≥ 2.
    geometric_diversity_theorem ↦ algebraic diversity condition. -/
theorem graph_independence_implies_algebraic_diversity
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block₁ block₂ obs₁ obs₂ : NodeType)
    (h_factor₁ : PathPred src block₁ obs₁)
    (h_factor₂ : PathPred src block₂ obs₂)
    (h_independent : ¬ PathPred src block₂ block₁)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_faith : Faithful PathPred src n2b branch_of)
    (h_comp  : Complete PathPred src n2b branch_of)
    (A : Agent)
    (h_mem₁ : n2b obs₁ ∈ A.memory) (h_mem₂ : n2b obs₂ ∈ A.memory) :
    2 ≤ effective_diversity branch_of A := by
  apply two_distinct_branches_ge_two branch_of A (n2b obs₁) (n2b obs₂) h_mem₁ h_mem₂
  intro h_eq
  have hb₁ : branch_of (n2b obs₁) = branch_of (n2b block₁) :=
    h_faith block₁ obs₁ h_factor₁
  have hb₂ : branch_of (n2b obs₂) = branch_of (n2b block₂) :=
    h_faith block₂ obs₂ h_factor₂
  exact h_independent (h_comp block₂ block₁ (by rw [← hb₁, ← hb₂]; exact h_eq))

/-- Graph blocking → algebraic blocking trap.
    Composes graph_blocking_implies_diversity_cap with blocking_trap. -/
theorem graph_blocking_implies_algebraic_trap
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block target : NodeType) (S : Finset NodeType)
    (h_target : ¬ PathPred src block target)
    (h_all : ∀ obs ∈ S, PathPred src block obs)
    (n2b : NodeType → Basin) (h_inj : Function.Injective n2b)
    (trajectory : ℕ → Agent)
    (h_restr : ∀ n B, B ∈ (trajectory n).memory → B ∈ S.image n2b) :
    ∀ n, n2b target ∉ (trajectory n).memory := by
  have h_out  : target ∉ S := fun h => h_target (h_all target h)
  have h_basin_out : n2b target ∉ S.image n2b :=
    node_not_in_S_gives_basin_not_in_image n2b h_inj S target h_out
  intro n h_in; exact h_basin_out (h_restr n (n2b target) h_in)


-- ============================================================
-- 12. DIRECTION A: ALGEBRAIC → GRAPH & FULL DUALITY
-- ============================================================

theorem same_branch_implies_path_factors
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block obs : NodeType)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_comp : Complete PathPred src n2b branch_of)
    (h_same : branch_of (n2b obs) = branch_of (n2b block)) :
    PathPred src block obs :=
  h_comp block obs h_same

theorem different_branches_implies_independence
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block obs : NodeType)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_faith : Faithful PathPred src n2b branch_of)
    (h_diff  : branch_of (n2b obs) ≠ branch_of (n2b block)) :
    ¬ PathPred src block obs := fun h => h_diff (h_faith block obs h)

/-- PathPred ↔ same branch under isomorphic assignment. -/
theorem graph_algebraic_biconditional
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block obs : NodeType)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_iso : IsomorphicAssignment PathPred src n2b branch_of) :
    PathPred src block obs ↔ branch_of (n2b obs) = branch_of (n2b block) :=
  ⟨h_iso.1 block obs, h_iso.2 block obs⟩

/-- collective_clarity_blocked ↔ single_branch_caps_diversity
    under isomorphic assignment. -/
theorem collective_blocking_duality
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block : NodeType) (S : Finset NodeType)
    (h_block_in_S : block ∈ S)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_iso : IsomorphicAssignment PathPred src n2b branch_of)
    (A : Agent) (h_memory : A.memory = S.image n2b) :
    (∀ obs ∈ S, PathPred src block obs) ↔ effective_diversity branch_of A ≤ 1 := by
  constructor
  · exact fun h => graph_blocking_implies_diversity_cap
        PathPred src block S h n2b branch_of h_iso.1 A h_memory
  · intro h_div obs h_obs
    apply h_iso.2 block obs
    have h_obs_mem := node_in_S_gives_basin_in_memory n2b S A h_memory obs h_obs
    have h_blk_mem := node_in_S_gives_basin_in_memory n2b S A h_memory block h_block_in_S
    have hx : branch_of (n2b obs)   ∈ A.memory.image branch_of :=
      Finset.mem_image.mpr ⟨n2b obs,   h_obs_mem, rfl⟩
    have hy : branch_of (n2b block) ∈ A.memory.image branch_of :=
      Finset.mem_image.mpr ⟨n2b block, h_blk_mem, rfl⟩
    unfold effective_diversity at h_div
    exact Finset.card_le_one.mp h_div _ hx _ hy

/-- Packaged biconditional: graph blocking ↔ algebraic diversity ≤ 1. -/
theorem translation_multi_tool
    (PathPred : NodeType → NodeType → NodeType → Prop)
    (src block : NodeType) (S : Finset NodeType)
    (h_block_in_S : block ∈ S)
    (n2b : NodeType → Basin) (branch_of : Basin → BranchId)
    (h_iso : IsomorphicAssignment PathPred src n2b branch_of)
    (A : Agent) (h_memory : A.memory = S.image n2b) :
    (∀ obs ∈ S, PathPred src block obs) ↔ effective_diversity branch_of A ≤ 1 :=
  collective_blocking_duality PathPred src block S h_block_in_S
    n2b branch_of h_iso A h_memory


-- ============================================================
-- 13. DIRECTION B: GRAPH WORLD TYPES
-- ============================================================

private def CsN : ℕ := 5
def CsNode := Fin CsN

abbrev CsBoard   := CsNode → Bool
abbrev CsTilt    := CsNode → ℝ

structure CsFingerprint where
  affected : Finset CsNode
  tilt_map : CsTilt
  drift    : ℝ

abbrev CsSignal (α : Type) := α → ℕ → Bool
abbrev CsBg     (α : Type) := α → ℕ → Bool

def csIterBoard (upd : CsBoard → CsBoard) : ℕ → CsBoard → CsNode → Bool
  | 0,     b, i => b i
  | n + 1, b, i => csIterBoard upd n (upd b) i

def csMkFp (b : CsBoard) (tilt : CsTilt) : CsFingerprint :=
  { affected := Finset.univ.filter (fun i => b i)
    tilt_map := tilt
    drift    := ∑ i : CsNode, if b i then (1 : ℝ) else 0 }

def csIterFp (upd : CsBoard → CsBoard) (tgn : CsBoard → CsTilt)
    (n : ℕ) (b₀ : CsBoard) : CsFingerprint :=
  csMkFp (csIterBoard upd n b₀) (tgn (csIterBoard upd n b₀))

def csFpDist (f₁ f₂ : CsFingerprint) : ℝ :=
  (∑ i : CsNode, (f₁.tilt_map i - f₂.tilt_map i) ^ 2) +
  (f₁.affected ∆ f₂.affected).card +
  (f₁.drift - f₂.drift) ^ 2

/-- +1 signal-on/bg-off; −1 signal-off/bg-on; 0 agree. -/
def csDev (α : Type) (bg : CsBg α) (sig : CsSignal α) (i : α) (t : ℕ) : ℤ :=
  if sig i t = true ∧ bg i t = false then 1
  else if sig i t = false ∧ bg i t = true then -1
  else 0

/-- Approximate clarity at tolerance ε_inv over window T. -/
def CsApproxClarity (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode) (ε_inv T : ℕ) : Prop :=
  ε_inv > 0 →
  ((Finset.range T).filter (fun t =>
    csDev CsNode bg sig obs t ≠ csDev CsNode bg sig src t)).card * ε_inv ≤ T

structure CsAccConds
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint) where
  persist_set   : Finset CsNode
  inj_time      : ℕ
  persists      : ∀ i ∈ persist_set,
      csIterBoard upd inj_time b₀ i = true ∧
      ∀ n ≥ inj_time, csIterBoard upd n b₀ i = true
  drift_bound   : ℝ
  bounded_drift : ∀ n, (csIterFp upd tgn n b₀).drift ≤ drift_bound
  sep_const     : ℝ
  sep_pos       : sep_const > 0
  additive_sep  : ∀ n, csFpDist (FBase n) (csIterFp upd tgn n b₀) ≥ sep_const


-- ============================================================
-- 14. DIRECTION B: ENCODING & FINGERPRINT BRIDGE
-- ============================================================

lemma in_affected_iff_active (b : CsBoard) (tilt : CsTilt) (i : CsNode) :
    i ∈ (csMkFp b tilt).affected ↔ b i = true := by
  simp [csMkFp, Finset.mem_filter]

/-- Under zero background, deviation ∈ {0, 1}; −1 is unreachable. -/
lemma zero_bg_dev (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (i : CsNode) (t : ℕ) (h_bg : bg i t = false) :
    csDev CsNode bg sig i t = if sig i t = true then 1 else 0 := by
  unfold csDev; cases h : sig i t <;> simp [h, h_bg]

lemma active_iff_dev_one
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (upd : CsBoard → CsBoard) (b₀ : CsBoard)
    (i : CsNode) (t : ℕ)
    (h_enc : sig i t = csIterBoard upd t b₀ i) (h_bg : bg i t = false) :
    csDev CsNode bg sig i t = 1 ↔ csIterBoard upd t b₀ i = true := by
  rw [zero_bg_dev bg sig i t h_bg]; simp [h_enc]
  cases csIterBoard upd t b₀ i <;> simp

/-- The symmetric difference term is dominated by csFpDist. -/
lemma sym_diff_le_fp_dist (f₁ f₂ : CsFingerprint) :
    ((f₁.affected ∆ f₂.affected).card : ℝ) ≤ csFpDist f₁ f₂ := by
  unfold csFpDist
  have h1 : 0 ≤ ∑ i : CsNode, (f₁.tilt_map i - f₂.tilt_map i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ (f₁.drift - f₂.drift) ^ 2 := sq_nonneg _
  positivity

lemma iter_fp_affected_eq_active
    (upd : CsBoard → CsBoard) (tgn : CsBoard → CsTilt)
    (n : ℕ) (b₀ : CsBoard) (i : CsNode) :
    i ∈ (csIterFp upd tgn n b₀).affected ↔ csIterBoard upd n b₀ i = true := by
  simp [csIterFp, in_affected_iff_active]


-- ============================================================
-- 15. DIRECTION B: PERSISTENCE → AGREEMENT → DISAGREEMENT BOUND
-- ============================================================

lemma persistent_node_dev_one
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (i : CsNode) (hi : i ∈ acc.persist_set)
    (h_enc : ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ t, bg i t = false) (t : ℕ) (ht : t ≥ acc.inj_time) :
    csDev CsNode bg sig i t = 1 := by
  rw [zero_bg_dev bg sig i t (h_bg t), if_pos]
  rw [h_enc]; exact (acc.persists i hi).2 t ht

theorem persistent_nodes_agree_after_injection
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode)
    (h_src : src ∈ acc.persist_set) (h_obs : obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false)
    (t : ℕ) (ht : t ≥ acc.inj_time) :
    csDev CsNode bg sig src t = csDev CsNode bg sig obs t := by
  rw [persistent_node_dev_one b₀ upd tgn FBase acc bg sig src h_src
        (h_enc src h_src) (h_bg src h_src) t ht,
      persistent_node_dev_one b₀ upd tgn FBase acc bg sig obs h_obs
        (h_enc obs h_obs) (h_bg obs h_obs) t ht]

theorem early_disagreement_bounded
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode)
    (h_src : src ∈ acc.persist_set) (h_obs : obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false) (T : ℕ) :
    ((Finset.range T).filter (fun t =>
        csDev CsNode bg sig obs t ≠ csDev CsNode bg sig src t)).card
    ≤ acc.inj_time := by
  have h_sub : (Finset.range T).filter (fun t =>
        csDev CsNode bg sig obs t ≠ csDev CsNode bg sig src t)
      ⊆ Finset.range acc.inj_time := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    by_contra h_not_lt; push_neg at h_not_lt
    exact ht.2 (persistent_nodes_agree_after_injection
      b₀ upd tgn FBase acc bg sig src obs h_src h_obs h_enc h_bg t h_not_lt)
  calc ((Finset.range T).filter _).card
      ≤ (Finset.range acc.inj_time).card := Finset.card_le_card h_sub
    _ = acc.inj_time                     := Finset.card_range acc.inj_time


-- ============================================================
-- 16. DIRECTION B: SEPARATION CERTIFIES CLARITY
-- ============================================================

theorem approx_clarity_eps_one_all_T
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode) (T : ℕ) :
    CsApproxClarity bg sig src obs 1 T := by
  intro _; simp only [Nat.mul_one]
  exact le_trans (Finset.card_filter_le _ _) (Finset.card_range T).le

theorem approx_clarity_large_T
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode)
    (h_src : src ∈ acc.persist_set) (h_obs : obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false)
    (ε_inv T : ℕ) (h_large : acc.inj_time * ε_inv ≤ T) :
    CsApproxClarity bg sig src obs ε_inv T := by
  intro _
  calc ((Finset.range T).filter _).card * ε_inv
      ≤ acc.inj_time * ε_inv :=
          Nat.mul_le_mul_right ε_inv
            (early_disagreement_bounded b₀ upd tgn FBase acc bg sig src obs
              h_src h_obs h_enc h_bg T)
    _ ≤ T := h_large

lemma ceil_inv_eq_one_of_sep_ge_one
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase) (h_sep_ge : acc.sep_const ≥ 1) :
    ⌈acc.sep_const⁻¹⌉₊ = 1 := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr; push_cast
    exact (inv_le_one₀ acc.sep_pos).mpr h_sep_ge
  · exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ceil_pos.mpr (inv_pos.mpr acc.sep_pos)).ne'

/-- SEPARATION CERTIFIES CLARITY — CONDITIONAL.
    For T ≥ inj_time × ⌈sep_const⁻¹⌉₊. -/
theorem separation_certifies_clarity_conditional
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode)
    (h_src : src ∈ acc.persist_set) (h_obs : obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false)
    (T : ℕ) (h_large : acc.inj_time * ⌈acc.sep_const⁻¹⌉₊ ≤ T) :
    CsApproxClarity bg sig src obs ⌈acc.sep_const⁻¹⌉₊ T :=
  approx_clarity_large_T b₀ upd tgn FBase acc bg sig src obs
    h_src h_obs h_enc h_bg ⌈acc.sep_const⁻¹⌉₊ T h_large

/-- SEPARATION CERTIFIES CLARITY — UNCONDITIONAL.
    When sep_const ≥ 1, holds for all T. -/
theorem separation_certifies_clarity_unconditional
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode)
    (h_src : src ∈ acc.persist_set) (h_obs : obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false)
    (h_sep_ge : acc.sep_const ≥ 1) :
    ∀ T, CsApproxClarity bg sig src obs ⌈acc.sep_const⁻¹⌉₊ T := by
  intro T
  rw [ceil_inv_eq_one_of_sep_ge_one b₀ upd tgn FBase acc h_sep_ge]
  exact approx_clarity_eps_one_all_T bg sig src obs T

/-- Conditional and unconditional forms together. -/
theorem separation_certifies_clarity_full
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (src obs : CsNode)
    (h_src : src ∈ acc.persist_set) (h_obs : obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false) :
    (∀ T, acc.inj_time * ⌈acc.sep_const⁻¹⌉₊ ≤ T →
          CsApproxClarity bg sig src obs ⌈acc.sep_const⁻¹⌉₊ T) ∧
    (acc.sep_const ≥ 1 → ∀ T, CsApproxClarity bg sig src obs ⌈acc.sep_const⁻¹⌉₊ T) :=
  ⟨fun T h_large =>
      separation_certifies_clarity_conditional b₀ upd tgn FBase acc bg sig src obs
        h_src h_obs h_enc h_bg T h_large,
   fun h_ge T =>
      separation_certifies_clarity_unconditional b₀ upd tgn FBase acc bg sig src obs
        h_src h_obs h_enc h_bg h_ge T⟩


-- ============================================================
-- 17. DIRECTION C: ADOPTION SET & COMPOUNDING DEFINITIONS
-- ============================================================

def adoptable_set (threshold : ℝ) (gains : Basin → ℝ) (Basins : Finset Basin) : Finset Basin :=
  Basins.filter (fun B => gains B > threshold)

def window_basins (Basins : Finset Basin) (gains : Basin → ℝ) (lo hi : ℝ) : Finset Basin :=
  Basins.filter (fun B => gains B > lo ∧ gains B ≤ hi)

/-- AdoptionDense: at least m basins in the δ-window above t. -/
def AdoptionDense (Basins : Finset Basin) (gains : Basin → ℝ) (t δ : ℝ) (m : ℕ) : Prop :=
  m ≤ (window_basins Basins gains t (t + δ)).card

/-- UniformlyDense: AdoptionDense at every threshold level. -/
def UniformlyDense (Basins : Finset Basin) (gains : Basin → ℝ) (δ : ℝ) (m : ℕ) : Prop :=
  ∀ t : ℝ, AdoptionDense Basins gains t δ m

noncomputable def threshold_at (t₀ rate : ℝ) (n : ℕ) : ℝ := t₀ - (n : ℝ) * rate
noncomputable def combined_rate (k_nat k_AI : ℕ) : ℝ :=
  0.10 + ((k_nat + k_AI : ℕ) : ℝ) * 0.05
def blocked_rate : ℝ := 0.10


-- ============================================================
-- 18. DIRECTION C: MONOTONICITY & PARTITION LEMMAS
-- ============================================================

theorem adoptable_antitone
    (t₁ t₂ : ℝ) (h : t₁ ≤ t₂) (gains : Basin → ℝ) (Basins : Finset Basin) :
    adoptable_set t₂ gains Basins ⊆ adoptable_set t₁ gains Basins := by
  intro B hB; simp only [adoptable_set, Finset.mem_filter] at hB ⊢
  exact ⟨hB.1, by linarith [hB.2]⟩

theorem adoptable_card_antitone
    (t₁ t₂ : ℝ) (h : t₁ ≤ t₂) (gains : Basin → ℝ) (Basins : Finset Basin) :
    (adoptable_set t₂ gains Basins).card ≤ (adoptable_set t₁ gains Basins).card :=
  Finset.card_le_card (adoptable_antitone t₁ t₂ h gains Basins)

lemma adoptable_splits_at_drop
    (Basins : Finset Basin) (gains : Basin → ℝ) (t_lo t_hi : ℝ) (h : t_lo < t_hi) :
    adoptable_set t_lo gains Basins =
    adoptable_set t_hi gains Basins ∪ window_basins Basins gains t_lo t_hi := by
  ext B; simp only [adoptable_set, window_basins, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro ⟨hB, hg⟩
    by_cases h1 : gains B > t_hi
    · exact Or.inl ⟨hB, h1⟩
    · push_neg at h1; exact Or.inr ⟨hB, hg, h1⟩
  · rintro (⟨hB, hg⟩ | ⟨hB, hg_lo, _⟩)
    · exact ⟨hB, by linarith⟩
    · exact ⟨hB, hg_lo⟩

lemma adoptable_hi_disjoint_window
    (Basins : Finset Basin) (gains : Basin → ℝ) (t_lo t_hi : ℝ) :
    Disjoint (adoptable_set t_hi gains Basins) (window_basins Basins gains t_lo t_hi) := by
  simp only [Finset.disjoint_filter, adoptable_set, window_basins, Finset.mem_filter]
  intro B _ h_hi _ _ h_le; linarith

theorem adoptable_card_split
    (Basins : Finset Basin) (gains : Basin → ℝ) (t_lo t_hi : ℝ) (h : t_lo < t_hi) :
    (adoptable_set t_lo gains Basins).card =
    (adoptable_set t_hi gains Basins).card +
    (window_basins Basins gains t_lo t_hi).card := by
  rw [adoptable_splits_at_drop Basins gains t_lo t_hi h]
  exact Finset.card_union_of_disjoint (adoptable_hi_disjoint_window Basins gains t_lo t_hi)


-- ============================================================
-- 19. DIRECTION C: THREE TIERS OF COMPOUNDING
-- ============================================================

-- ── TIER 1: LINEAR ──────────────────────────────────────────

theorem combined_exceeds_blocked (k_nat k_AI : ℕ) (h : k_nat + k_AI ≥ 1) :
    blocked_rate < combined_rate k_nat k_AI := by
  unfold blocked_rate combined_rate
  have hge : ((k_nat + k_AI : ℕ) : ℝ) ≥ 1 := by exact_mod_cast h
  nlinarith

theorem combined_threshold_lower
    (t₀ : ℝ) (k_nat k_AI : ℕ) (h : k_nat + k_AI ≥ 1) (n : ℕ) (hn : n ≥ 1) :
    threshold_at t₀ (combined_rate k_nat k_AI) n < threshold_at t₀ blocked_rate n := by
  unfold threshold_at
  have h_rate := combined_exceeds_blocked k_nat k_AI h
  have h_n : (n : ℝ) ≥ 1 := by exact_mod_cast hn
  have h_n_pos : (n : ℝ) > 0 := by linarith
  nlinarith [mul_lt_mul_of_pos_left h_rate h_n_pos]

theorem linear_gap_formula (t₀ : ℝ) (k_nat k_AI : ℕ) (n : ℕ) :
    threshold_at t₀ blocked_rate n - threshold_at t₀ (combined_rate k_nat k_AI) n
    = (n : ℝ) * ((k_nat + k_AI : ℕ) : ℝ) * 0.05 := by
  unfold threshold_at blocked_rate combined_rate; ring

theorem linear_gap_unbounded
    (t₀ : ℝ) (k_nat k_AI : ℕ) (hk : k_nat + k_AI ≥ 1) (T_target : ℝ) :
    ∃ n : ℕ, threshold_at t₀ (combined_rate k_nat k_AI) n < T_target := by
  have h_rate_pos : combined_rate k_nat k_AI > 0 :=
    lt_trans (by unfold blocked_rate; norm_num) (combined_exceeds_blocked k_nat k_AI hk)
  obtain ⟨n, hn⟩ := exists_nat_gt ((t₀ - T_target) / combined_rate k_nat k_AI)
  exact ⟨n, by
    unfold threshold_at
    have h_n : (n : ℝ) > (t₀ - T_target) / combined_rate k_nat k_AI := by exact_mod_cast hn
    linarith [(div_lt_iff h_rate_pos).mp h_n]⟩

-- ── TIER 2: ONE-STEP DENSITY FEEDBACK ───────────────────────

theorem density_enables_new_adoptions
    (Basins : Finset Basin) (gains : Basin → ℝ)
    (t_lo t_hi : ℝ) (h_drop : t_lo < t_hi) (m : ℕ)
    (h_dense : AdoptionDense Basins gains t_lo (t_hi - t_lo) m) :
    (adoptable_set t_hi gains Basins).card + m ≤ (adoptable_set t_lo gains Basins).card := by
  rw [adoptable_card_split Basins gains t_lo t_hi h_drop]
  have h_eq : window_basins Basins gains t_lo (t_lo + (t_hi - t_lo)) =
              window_basins Basins gains t_lo t_hi := by simp [window_basins]; ring_nf
  unfold AdoptionDense at h_dense; rw [h_eq] at h_dense; omega

theorem one_cycle_multiplier_exceeds_one (m : ℕ) (hm : m ≥ 1) (δ : ℝ) (hδ : δ > 0) :
    δ < (1 + (m : ℝ)) * δ := by
  have hm' : (m : ℝ) ≥ 1 := by exact_mod_cast hm
  nlinarith

-- ── TIER 3: ITERATED COMPOUNDING — EXPONENTIAL ──────────────

lemma pow_ge_linear (m : ℕ) (hm : m ≥ 1) : ∀ k : ℕ, k ≤ (1 + m)^k := by
  intro k; induction k with
  | zero => simp
  | succ k ih =>
    have hm_pos : 0 < 1 + m := by omega
    have h_one  : 1 ≤ (1 + m)^k := Nat.one_le_pow k (1 + m) hm_pos
    calc k + 1 ≤ (1 + m)^k + 1  := by omega
      _ ≤ (1 + m)^k * 2          := by nlinarith
      _ ≤ (1 + m)^k * (1 + m)    := by nlinarith
      _ = (1 + m)^(k + 1)        := by ring

theorem compounding_exceeds_linear
    (k : ℕ) (m : ℕ) (hm : m ≥ 1) (δ₀ : ℝ) (hδ : δ₀ ≥ 0) :
    (k : ℝ) * δ₀ ≤ (1 + (m : ℝ))^k * δ₀ := by
  have h : (k : ℝ) ≤ (1 + (m : ℝ))^k := by exact_mod_cast pow_ge_linear m hm k
  nlinarith

/-- Any target threshold reachable in finite compounding cycles. -/
theorem compounding_reaches_any_target
    (t₀ T δ₀ : ℝ) (hδ : δ₀ > 0) (m : ℕ) (hm : m ≥ 1) :
    ∃ k : ℕ, t₀ - (1 + (m : ℝ))^k * δ₀ < T := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((t₀ - T) / δ₀)
  use k
  have h_cast : (k : ℝ) ≤ (1 + (m : ℝ))^k := by exact_mod_cast pow_ge_linear m hm k
  have h1 : t₀ - T < (k : ℝ) * δ₀ := by rwa [gt_iff_lt, lt_div_iff hδ] at hk
  linarith [mul_le_mul_of_nonneg_right h_cast (le_of_lt hδ)]

theorem compounding_dominates_linear_trajectory
    (t₀ δ₀ : ℝ) (hδ : δ₀ > 0) (m : ℕ) (hm : m ≥ 1) (k : ℕ) (hk : k ≥ 1) :
    t₀ - (1 + (m : ℝ))^k * δ₀ ≤ t₀ - (k : ℝ) * δ₀ := by
  have h : (k : ℝ) ≤ (1 + (m : ℝ))^k := by exact_mod_cast pow_ge_linear m hm k
  nlinarith


-- ============================================================
-- 20. DIRECTION C: COMPOUNDING SYNTHESIS
-- ============================================================

theorem compounding_dominance
    (k_nat k_AI : ℕ) (hk : k_nat + k_AI ≥ 1)
    (δ₀ : ℝ) (hδ : δ₀ > 0)
    (Basins : Finset Basin) (gains : Basin → ℝ)
    (m : ℕ) (hm : m ≥ 1)
    (benefit : ℝ) (h_benefit : benefit > 0)
    (t₀ T_target : ℝ) :
    threshold_at t₀ (combined_rate k_nat k_AI) 1 < threshold_at t₀ blocked_rate 1
    ∧ δ₀ < (1 + (m : ℝ)) * δ₀
    ∧ ∃ k : ℕ, t₀ - (1 + (m : ℝ))^k * δ₀ < T_target :=
  ⟨combined_threshold_lower t₀ k_nat k_AI hk 1 (le_refl 1),
   one_cycle_multiplier_exceeds_one m hm δ₀ hδ,
   compounding_reaches_any_target t₀ T_target δ₀ hδ m hm⟩

theorem compounding_beats_linear_to_target
    (t₀ T_target δ₀ : ℝ) (hδ : δ₀ > 0) (hT : T_target < t₀)
    (m : ℕ) (hm : m ≥ 1) :
    ∃ k : ℕ,
      t₀ - (1 + (m : ℝ))^k * δ₀ < T_target ∧
      t₀ - (k : ℝ) * δ₀ ≥ T_target - δ₀ := by
  obtain ⟨k, hk⟩ := compounding_reaches_any_target t₀ T_target δ₀ hδ m hm
  exact ⟨k, hk, by
    have h_pow : (k : ℝ) ≤ (1 + (m : ℝ))^k := by exact_mod_cast pow_ge_linear m hm k
    nlinarith⟩


-- ============================================================
-- 21. GRAND SYNTHESIS
-- ============================================================

/-
  Chain from graph persistence to finite-cycle target reachability:

    DIRECTION B: CsAccConds with sep_const ≥ 1
      → ApproxClarity for all T

    DIRECTION A: clarity + isomorphic assignment + independent paths
      → effective_diversity ≥ 2

    FOUNDATION: diversity ≥ 2
      → combined_rate > blocked_rate  (Tier 1)

    DIRECTION C: combined rate + positive density
      → (1 + m)^k multiplier  (Tier 3)
      → any target reachable in finite cycles

  The three conditions are independent:
    blocking resolved → reachable set expands → density activates
    infrastructure    → per_step_net > 0 → cycles net positive
    diversity ≥ 2     → combined rate > blocked rate
-/
theorem grand_unified_theorem
    (b₀ : CsBoard) (upd : CsBoard → CsBoard)
    (tgn : CsBoard → CsTilt) (FBase : ℕ → CsFingerprint)
    (acc : CsAccConds b₀ upd tgn FBase)
    (bg : CsBg CsNode) (sig : CsSignal CsNode)
    (cs_src cs_obs : CsNode)
    (h_cs_src : cs_src ∈ acc.persist_set)
    (h_cs_obs : cs_obs ∈ acc.persist_set)
    (h_enc : ∀ i ∈ acc.persist_set, ∀ n, sig i n = csIterBoard upd n b₀ i)
    (h_bg  : ∀ i ∈ acc.persist_set, ∀ t, bg i t = false)
    (h_sep_ge : acc.sep_const ≥ 1)
    (PathPred  : NodeType → NodeType → NodeType → Prop)
    (n2b       : NodeType → Basin)
    (branch_of : Basin → BranchId)
    (h_iso     : IsomorphicAssignment PathPred src_n n2b branch_of)
    (src_n block₁ block₂ obs₁ obs₂ : NodeType)
    (h_factor₁    : PathPred src_n block₁ obs₁)
    (h_factor₂    : PathPred src_n block₂ obs₂)
    (h_independent : ¬ PathPred src_n block₂ block₁)
    (A_ai : Agent)
    (h_mem₁ : n2b obs₁ ∈ A_ai.memory) (h_mem₂ : n2b obs₂ ∈ A_ai.memory)
    (r c_high vcr benefit : ℝ)
    (h_raise   : r ≤ c_high) (h_b_pos : benefit > 0)
    (k_nat k_AI : ℕ) (hk : k_nat + k_AI ≥ 1)
    (δ₀ : ℝ) (hδ : δ₀ > 0)
    (m : ℕ) (hm : m ≥ 1)
    (t₀ T_target : ℝ) :
    (∀ T, CsApproxClarity bg sig cs_src cs_obs ⌈acc.sep_const⁻¹⌉₊ T)
    ∧ 2 ≤ effective_diversity branch_of A_ai
    ∧ per_step_net r c_high vcr benefit > 0
    ∧ (∃ k : ℕ, t₀ - (1 + (m : ℝ))^k * δ₀ < T_target) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact separation_certifies_clarity_unconditional b₀ upd tgn FBase acc bg sig
        cs_src cs_obs h_cs_src h_cs_obs h_enc h_bg h_sep_ge
  · exact graph_independence_implies_algebraic_diversity PathPred src_n block₁ block₂
        obs₁ obs₂ h_factor₁ h_factor₂ h_independent n2b branch_of
        h_iso.1 h_iso.2 A_ai h_mem₁ h_mem₂
  · exact rate_within_capacity_beneficial r c_high vcr benefit h_raise h_b_pos
  · exact compounding_reaches_any_target t₀ T_target δ₀ hδ m hm


-- ============================================================
-- 22. MULTI-AGENT EXPOSURE: ATTRACTOR ESCAPE AND COMPOUNDING
-- ============================================================
/-
  Formal conditions under which inter-attractor probing breaks
  the blocking trap and activates the compounding chain.

  §4's blocking_trap establishes that an agent confined to a
  single reachable set never reaches basins outside it, regardless
  of trajectory length.

  This section formalises two conditions that together dissolve
  the trap:
    (1) The agent probes an agent in an independent self-attractor
        (distinct causal branch, witness basins on different branches).
    (2) The opened adoption window contains viable basins (h_dense).

  Given both, the compounding chain activates: any target threshold
  is reachable in finite cycles.

  WHY h_dense IS CARRIED AS A HYPOTHESIS

  h_dense asserts that viable basins exist in the window between
  the pre-probe and post-probe thresholds.  This is a geometric
  condition on the basin space that cannot be derived from the
  attractor definitions alone.  It is the boundary of what the
  formal system can establish from first principles.

  This follows the pattern of h_dist_from_sig in InterfaceConfig.lean
  and SeparationCertifiesClarity in CausalSignature.lean: structural
  assumptions are named at every call site rather than hidden.

  When h_dense holds, the logical chain fires unconditionally.
  Whether h_dense holds is determined by the geometry of the
  specific basin space, not by the formal system.
-/

/-- An agent whose effective causal diversity is at most 1:
    all memory maps to a single branch under branch_of. -/
def in_own_attractor (branch_of : Basin → BranchId) (A : Agent) : Prop :=
  effective_diversity branch_of A ≤ 1

/-- Two agents each with effective diversity ≤ 1, with witness
    basins on distinct branches.  Their memories arise from
    structurally separate causal branches. -/
def IndependentAttractors (branch_of : Basin → BranchId) (A B : Agent) : Prop :=
  in_own_attractor branch_of A ∧
  in_own_attractor branch_of B ∧
  ∃ (a b : Basin), a ∈ A.memory ∧ b ∈ B.memory ∧ branch_of a ≠ branch_of b

/-- The result of agent A observing agent B's memory:
    memory becomes the union; exposure count increments. -/
def probe_agent (A B : Agent) : Agent :=
  { exposure_count := A.exposure_count + 1
    memory         := A.memory ∪ B.memory
    utility        := A.utility
    cost           := A.cost }

/-- IndependentAttractors is symmetric in A and B. -/
theorem independent_attractors_symmetric
    (branch_of : Basin → BranchId) (A B : Agent)
    (h : IndependentAttractors branch_of A B) :
    IndependentAttractors branch_of B A := by
  obtain ⟨hA, hB, a, b, ha, hb, h_ne⟩ := h
  exact ⟨hB, hA, b, a, hb, ha, h_ne.symm⟩

/-- Probing an independent agent achieves effective_diversity ≥ 2:
    the union of memories contains witnesses on distinct branches. -/
theorem probe_breaks_attractor_trap
    (branch_of : Basin → BranchId) (A B : Agent)
    (h : IndependentAttractors branch_of A B) :
    2 ≤ effective_diversity branch_of (probe_agent A B) := by
  obtain ⟨_, _, a, b, ha, hb, h_ne⟩ := h
  exact two_distinct_branches_ge_two branch_of (probe_agent A B) a b
    (Finset.mem_union_left  _ ha)
    (Finset.mem_union_right _ hb)
    h_ne

/-- Probing strictly lowers the true threshold: −0.10 from the
    exposure increment, at least −0.05 from the diversity jump
    (≤1 → ≥2), total drop ≥ 0.15. -/
theorem probe_lowers_true_threshold
    (branch_of : Basin → BranchId) (A B : Agent)
    (h : IndependentAttractors branch_of A B) :
    true_threshold branch_of (probe_agent A B) <
    true_threshold branch_of A := by
  have h_pre  : effective_diversity branch_of A ≤ 1 := h.1
  have h_post : 2 ≤ effective_diversity branch_of (probe_agent A B) :=
    probe_breaks_attractor_trap branch_of A B h
  unfold true_threshold probe_agent
  have hpre  : (effective_diversity branch_of A).to_real ≤ 1 := by
    exact_mod_cast h_pre
  have hpost : (2 : ℝ) ≤ (effective_diversity branch_of
                  (probe_agent A B)).to_real := by
    exact_mod_cast h_post
  push_cast; linarith

/-- The threshold drop is at least 0.15:
    0.10 from the exposure count; 0.05 from the diversity jump. -/
theorem probe_threshold_drop_bound
    (branch_of : Basin → BranchId) (A B : Agent)
    (h : IndependentAttractors branch_of A B) :
    0.15 ≤ true_threshold branch_of A -
           true_threshold branch_of (probe_agent A B) := by
  have h_pre  : effective_diversity branch_of A ≤ 1 := h.1
  have h_post : 2 ≤ effective_diversity branch_of (probe_agent A B) :=
    probe_breaks_attractor_trap branch_of A B h
  unfold true_threshold probe_agent
  have hpre  : (effective_diversity branch_of A).to_real ≤ 1 := by
    exact_mod_cast h_pre
  have hpost : (2 : ℝ) ≤ (effective_diversity branch_of
                  (probe_agent A B)).to_real := by
    exact_mod_cast h_post
  push_cast; linarith

/-- Under h_dense, the threshold drop makes m additional basins
    adoptable: the post-probe adoptable set exceeds the pre-probe
    set by at least m. -/
theorem probe_opens_adoption_window
    (branch_of : Basin → BranchId) (A B : Agent)
    (h_indep : IndependentAttractors branch_of A B)
    (Basins : Finset Basin) (gains : Basin → ℝ) (m : ℕ)
    (h_dense : AdoptionDense Basins gains
                 (true_threshold branch_of (probe_agent A B))
                 (true_threshold branch_of A -
                  true_threshold branch_of (probe_agent A B)) m) :
    (adoptable_set (true_threshold branch_of A) gains Basins).card + m
      ≤ (adoptable_set (true_threshold branch_of (probe_agent A B))
                       gains Basins).card :=
  density_enables_new_adoptions Basins gains
    (true_threshold branch_of (probe_agent A B))
    (true_threshold branch_of A)
    (probe_lowers_true_threshold branch_of A B h_indep)
    m h_dense

/-- When A probes B and B probes A, both achieve diversity ≥ 2.
    Follows by symmetry of IndependentAttractors. -/
theorem mutual_probe_both_escape
    (branch_of : Basin → BranchId) (A B : Agent)
    (h : IndependentAttractors branch_of A B) :
    2 ≤ effective_diversity branch_of (probe_agent A B) ∧
    2 ≤ effective_diversity branch_of (probe_agent B A) :=
  ⟨probe_breaks_attractor_trap branch_of A B h,
   probe_breaks_attractor_trap branch_of B A
     (independent_attractors_symmetric branch_of A B h)⟩

/-
  EXPOSURE COMPOUNDING THEOREM — CAPSTONE

  Three consequences of a single inter-attractor probe event:

    (I)   effective_diversity ≥ 2  (blocking trap broken)
    (II)  adoptable set grows by m  (h_dense activates window)
    (III) ∃ k finite cycles reach any target  (compounding)

  Parts (I) and (II) follow from IndependentAttractors and h_dense.
  Part (III) follows from m ≥ 1 and δ₀ > 0 via Tier 3 compounding.

  When h_dense does not hold (empty basin window), parts (I) and (II)
  still follow from the probe; part (III) requires a non-empty window.
-/
theorem exposure_compounds_learning
    (branch_of : Basin → BranchId)
    (A B : Agent)
    (h_indep : IndependentAttractors branch_of A B)
    (Basins : Finset Basin) (gains : Basin → ℝ)
    (m : ℕ) (hm : m ≥ 1)
    (δ₀ : ℝ) (hδ : δ₀ > 0)
    (t₀ T_target : ℝ)
    (h_dense : AdoptionDense Basins gains
                 (true_threshold branch_of (probe_agent A B))
                 (true_threshold branch_of A -
                  true_threshold branch_of (probe_agent A B)) m) :
    2 ≤ effective_diversity branch_of (probe_agent A B)
    ∧
    (adoptable_set (true_threshold branch_of A) gains Basins).card + m
      ≤ (adoptable_set (true_threshold branch_of (probe_agent A B))
                       gains Basins).card
    ∧
    ∃ k : ℕ, t₀ - (1 + (m : ℝ))^k * δ₀ < T_target :=
  ⟨probe_breaks_attractor_trap branch_of A B h_indep,
   probe_opens_adoption_window branch_of A B h_indep Basins gains m h_dense,
   compounding_reaches_any_target t₀ T_target δ₀ hδ m hm⟩


-- ============================================================
-- 23. FLUX NAVIGATION: DISSOLVING THE NP-HARD BLOCKING MAZE
-- ============================================================
/-
  Bridge between UnifiedFluxDynamics (v2) / MonkPath (v2)
  and the algebraic blocking/compounding framework.

  THE BLOCKING MAZE (NP-HARD FRAMING):
    §4's blocking_trap confines a trajectory to a single reachable
    set regardless of trajectory length.  In a general causal graph,
    finding a path to a different causal branch by explicit path
    enumeration is NP-hard: there is no known polynomial-time
    algorithm for the general "blocked basin reachability" problem.

  THE FLUX SOLUTION:
    UnifiedFluxDynamics (v2) proves that wherever 3 or more distinct
    attractor basins coexist (NestedEcology), flux necessarily emerges
    at states from which multiple basins are reachable at different
    capture times.  This is structural — the dynamics force it.

    MonkPath (v2)'s weighted_flux integrates local signal with
    inverse-distance anticipation from all safe states, making this
    flux observable.  The agent only moves when anticipated gain
    exceeds flux_threshold, always climbing the weighted_flux gradient.

    The key bridge (FluxAligned): if the flux signal correctly
    identifies causal branch boundaries, then:

      (1) Any basin with detectable flux is OUTSIDE the blocked branch
          — it cannot be inside without contradicting SingleBranchMemory.
          Cost: one flux query.  No maze enumeration required.

      (2) Adding that basin to memory immediately gives diversity ≥ 2.
          The blocking trap dissolves in a single step.

      (3) Diversity ≥ 2 activates the compounding chain (§19–20):
          combined_rate > blocked_rate → exponential threshold drop
          → any target threshold reachable in finite cycles.

  FluxAligned is an empirical assumption (like h_dense in §22):
    NestedCausalEcology guarantees flux *exists* (UnifiedFluxDynamics
    §2: flux_emerges_from_nested_instability);
    FluxAligned asserts the sensor correctly maps that flux to causal
    branch boundaries.  When both hold, the NP-hard search collapses
    to gradient ascent along the flux field.
-/

/-- Observable flux signal over the algebraic basin space.
    Discrete analog of MonkPath's weighted_flux and flux_sense. -/
structure BasinFluxSignal where
  flux_sense     : Basin → ℕ
  flux_threshold : ℕ

/-- Flux alignment: suprathreshold flux reliably indicates basins
    outside the currently blocked causal branch.  This is the bridge
    between flux emergence (NestedCausalEcology) and causal structure.
    Analogous to h_dense (§22) and h_dist_from_sig (CausalSignature):
    a structural assumption named explicitly rather than hidden. -/
def FluxAligned (signal : BasinFluxSignal)
    (branch_of : Basin → BranchId) (blocked_branch : BranchId) : Prop :=
  ∀ B : Basin,
    signal.flux_sense B ≥ signal.flux_threshold →
    branch_of B ≠ blocked_branch

/-- Discrete NestedEcology: at least 3 causally distinct basins exist.
    Mirrors UnifiedFluxDynamics §1's NestedEcology, instantiated over
    the algebraic Basin/BranchId types.  This is the structural
    condition that guarantees flux emergence in the dynamics. -/
def NestedCausalEcology (all_basins : Finset Basin)
    (branch_of : Basin → BranchId) : Prop :=
  ∃ B₁ B₂ B₃ : Basin,
    B₁ ∈ all_basins ∧ B₂ ∈ all_basins ∧ B₃ ∈ all_basins ∧
    branch_of B₁ ≠ branch_of B₂ ∧
    branch_of B₂ ≠ branch_of B₃ ∧
    branch_of B₁ ≠ branch_of B₃

/-- SingleBranchMemory: all of the agent's current memory lies in one
    causal branch.  The algebraic form of the blocking trap (§4). -/
def SingleBranchMemory (A : Agent)
    (branch_of : Basin → BranchId) (blocked_branch : BranchId) : Prop :=
  ∀ B ∈ A.memory, branch_of B = blocked_branch

/-- Flux alignment + single-branch confinement → any flux-bearing basin
    is necessarily outside the agent's current memory.
    The logical contradiction: if a flux-bearing basin were in memory,
    it would have to be both in blocked_branch (by SingleBranchMemory)
    and not in blocked_branch (by FluxAligned).  No path search needed. -/
theorem flux_basin_not_in_blocked_memory
    (branch_of : Basin → BranchId) (A : Agent)
    (blocked_branch : BranchId)
    (h_single : SingleBranchMemory A branch_of blocked_branch)
    (signal : BasinFluxSignal)
    (h_aligned : FluxAligned signal branch_of blocked_branch)
    (B_flux : Basin)
    (h_flux : signal.flux_sense B_flux ≥ signal.flux_threshold) :
    B_flux ∉ A.memory := fun h_in =>
  absurd (h_single B_flux h_in) (h_aligned B_flux h_flux)

/-- NestedCausalEcology guarantees the existence of a detectable
    flux basin outside the blocked branch.
    Among three pairwise-distinct branches, at most one equals
    blocked_branch; the remaining two are cross-branch, and the
    aligned flux sensor detects at least one of them.
    Bridges UnifiedFluxDynamics §2 (flux_emerges_from_nested_instability)
    to the algebraic blocking structure. -/
theorem nested_ecology_yields_flux_basin
    (branch_of : Basin → BranchId) (A : Agent)
    (all_basins : Finset Basin)
    (blocked_branch : BranchId)
    (h_single : SingleBranchMemory A branch_of blocked_branch)
    (h_nested : NestedCausalEcology all_basins branch_of)
    (signal : BasinFluxSignal)
    (h_aligned : FluxAligned signal branch_of blocked_branch)
    (h_coverage : ∀ B ∈ all_basins,
        branch_of B ≠ blocked_branch →
        signal.flux_sense B ≥ signal.flux_threshold) :
    ∃ B_flux ∈ all_basins,
        signal.flux_sense B_flux ≥ signal.flux_threshold ∧
        B_flux ∉ A.memory := by
  obtain ⟨B₁, B₂, B₃, h₁, h₂, h₃, h12, h23, h13⟩ := h_nested
  by_cases hb₁ : branch_of B₁ = blocked_branch
  · by_cases hb₂ : branch_of B₂ = blocked_branch
    · -- branch_of B₁ = branch_of B₂ = blocked_branch contradicts h12
      exact absurd (hb₁.trans hb₂.symm) h12
    · exact ⟨B₂, h₂, h_coverage B₂ h₂ hb₂,
             flux_basin_not_in_blocked_memory branch_of A blocked_branch
               h_single signal h_aligned B₂ (h_coverage B₂ h₂ hb₂)⟩
  · exact ⟨B₁, h₁, h_coverage B₁ h₁ hb₁,
           flux_basin_not_in_blocked_memory branch_of A blocked_branch
             h_single signal h_aligned B₁ (h_coverage B₁ h₁ hb₁)⟩

/-- One flux-guided step achieves effective_diversity ≥ 2.
    The agent adds a single flux-bearing basin to memory.  The branch
    of that basin differs from blocked_branch (by FluxAligned), while
    existing memory is confined to blocked_branch (SingleBranchMemory).
    Two_distinct_branches_ge_two closes the diversity gap immediately. -/
theorem flux_step_achieves_diversity
    (branch_of : Basin → BranchId) (A : Agent)
    (h_nonempty : A.memory.Nonempty)
    (blocked_branch : BranchId)
    (h_single : SingleBranchMemory A branch_of blocked_branch)
    (signal : BasinFluxSignal)
    (h_aligned : FluxAligned signal branch_of blocked_branch)
    (B_flux : Basin)
    (h_flux : signal.flux_sense B_flux ≥ signal.flux_threshold) :
    2 ≤ effective_diversity branch_of
          { A with memory         := A.memory ∪ {B_flux}
                  exposure_count := A.exposure_count + 1 } := by
  obtain ⟨B_old, h_old⟩ := h_nonempty
  apply two_distinct_branches_ge_two branch_of _ B_old B_flux
  · exact Finset.mem_union_left _ h_old
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self B_flux)
  · intro h_eq
    exact (h_aligned B_flux h_flux) (h_eq ▸ h_single B_old h_old)

/-- FLUX DISSOLVES THE TRAP AND ACTIVATES COMPOUNDING — CAPSTONE §23

    Full chain from NestedCausalEcology to finite-cycle target
    reachability via one flux-guided step:

      NestedCausalEcology + FluxAligned + h_coverage
        → B_flux exists outside blocked memory    (nested_ecology_yields_flux_basin)
      B_flux ∉ A.memory                           (flux_basin_not_in_blocked_memory)
      One step along the flux gradient
        → diversity ≥ 2                           (flux_step_achieves_diversity)
      Diversity ≥ 2 activates §19–20 compounding
        → any target reachable in finite cycles   (compounding_reaches_any_target)

    The NP-hard maze is navigated via O(1) flux queries rather than
    exponential path enumeration.  The flux field — guaranteed to exist
    by NestedCausalEcology — encodes the escape route. -/
theorem flux_dissolves_trap_activates_compounding
    (branch_of : Basin → BranchId) (A : Agent)
    (h_nonempty : A.memory.Nonempty)
    (blocked_branch : BranchId)
    (h_single : SingleBranchMemory A branch_of blocked_branch)
    (all_basins : Finset Basin)
    (h_nested : NestedCausalEcology all_basins branch_of)
    (signal : BasinFluxSignal)
    (h_aligned : FluxAligned signal branch_of blocked_branch)
    (h_coverage : ∀ B ∈ all_basins,
        branch_of B ≠ blocked_branch →
        signal.flux_sense B ≥ signal.flux_threshold)
    (δ₀ : ℝ) (hδ : δ₀ > 0) (m : ℕ) (hm : m ≥ 1)
    (t₀ T_target : ℝ) :
    ∃ B_flux : Basin,
      B_flux ∉ A.memory ∧
      2 ≤ effective_diversity branch_of
            { A with memory         := A.memory ∪ {B_flux}
                    exposure_count := A.exposure_count + 1 } ∧
      ∃ k : ℕ, t₀ - (1 + (m : ℝ))^k * δ₀ < T_target := by
  obtain ⟨B_flux, _h_in, h_flux, h_not_in⟩ :=
    nested_ecology_yields_flux_basin branch_of A all_basins blocked_branch
      h_single h_nested signal h_aligned h_coverage
  exact ⟨B_flux, h_not_in,
         flux_step_achieves_diversity branch_of A h_nonempty blocked_branch
           h_single signal h_aligned B_flux h_flux,
         compounding_reaches_any_target t₀ T_target δ₀ hδ m hm⟩
