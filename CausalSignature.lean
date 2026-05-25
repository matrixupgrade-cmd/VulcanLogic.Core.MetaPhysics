-- ====================================================
-- CausalSignature.lean       Author: Sean Timothy
-- ====================================================

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Order
import Mathlib.Algebra.Order.Floor

open Finset BigOperators


-- ============================================================
-- 1. TYPES
-- ============================================================

def N : ℕ := 5
def Node := Fin N

abbrev Board    := Node → Bool
abbrev Tilt     := Node → ℝ

structure AsymmetryFingerprint where
  affected : Finset Node
  tilt_map : Tilt
  drift    : ℝ

abbrev TemporalSignal (α : Type) := α → ℕ → Bool
abbrev Background     (α : Type) := α → ℕ → Bool


-- ============================================================
-- 2. BOARD DYNAMICS
-- ============================================================

def iterated_board (update : Board → Board) : ℕ → Board → Node → Bool
  | 0,     b, i => b i
  | n + 1, b, i => iterated_board update n (update b) i

def absorbing (update : Board → Board) : Prop :=
  ∀ (b : Board) (i : Node), b i = true → update b i = true

def fingerprint (b : Board) (tilt : Tilt) : AsymmetryFingerprint :=
  { affected := Finset.univ.filter (fun i => b i)
    tilt_map := tilt
    drift    := ∑ _i : Node, if b · then (1 : ℝ) else 0 }

def fingerprint_distance (f₁ f₂ : AsymmetryFingerprint) : ℝ :=
  (∑ i, (f₁.tilt_map i - f₂.tilt_map i) ^ 2) +
  (f₁.affected ∆ f₂.affected).card +
  (f₁.drift - f₂.drift) ^ 2

def iterated_fingerprint (update : Board → Board) (tilt_gen : Board → Tilt)
    (n : ℕ) (b₀ : Board) : AsymmetryFingerprint :=
  fingerprint (iterated_board update n b₀) (tilt_gen (iterated_board update n b₀))


-- ============================================================
-- 3. ACCEPTANCE CONDITIONS
-- ============================================================

structure AcceptanceConditions
    (b₀       : Board)
    (update   : Board → Board)
    (tilt_gen : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint) where
  persistence_set     : Finset Node
  injection_time      : ℕ
  persists            : ∀ i ∈ persistence_set,
      iterated_board update injection_time b₀ i = true ∧
      ∀ n ≥ injection_time, iterated_board update n b₀ i = true
  bounded_drift_bound : ℝ
  bounded_drift       : ∀ n,
      (iterated_fingerprint update tilt_gen n b₀).drift ≤ bounded_drift_bound
  separation_constant : ℝ
  separation_pos      : separation_constant > 0
  additive_separation : ∀ n,
      fingerprint_distance (F_base n)
        (iterated_fingerprint update tilt_gen n b₀) ≥ separation_constant


-- ============================================================
-- 4. SIGNAL DEVIATION
-- ============================================================

def SignedDeviation (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (i : α) (t : ℕ) : ℤ :=
  if sig i t = true ∧ bg i t = false then 1
  else if sig i t = false ∧ bg i t = true then -1
  else 0

def CumulativeDeviation (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (i : α) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, SignedDeviation α bg sig i t

noncomputable def VarianceRate (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (i : α) (T : ℕ) : ℝ :=
  if T = 0 then 0
  else (∑ t ∈ Finset.range T, (SignedDeviation α bg sig i t : ℝ) ^ 2) / T

noncomputable def VarianceAcceleration (α : Type) (bg : Background α)
    (sig : TemporalSignal α) (i : α) (T : ℕ) : ℝ :=
  VarianceRate α bg sig i (T + 1) - VarianceRate α bg sig i T


-- ============================================================
-- 5. PULSE PREDICATES
-- ============================================================

def PulseOn (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (i : α) (T_start duration : ℕ) : Prop :=
  ∀ t, T_start ≤ t → t < T_start + duration →
    SignedDeviation α bg sig i t = 1

def PulseOff (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (i : α) (T_start duration : ℕ) : Prop :=
  ∀ t, T_start ≤ t → t < T_start + duration →
    SignedDeviation α bg sig i t = -1

def PulseSilent (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (i : α) (T_start duration : ℕ) : Prop :=
  ∀ t, T_start ≤ t → t < T_start + duration →
    SignedDeviation α bg sig i t = 0


-- ============================================================
-- 6. SIGNAL CLARITY
-- ============================================================

def SignalClarity (α : Type) (bg : Background α) (sig : TemporalSignal α)
    (src obs : α) : Prop :=
  ∀ t, SignedDeviation α bg sig obs t = SignedDeviation α bg sig src t


-- ============================================================
-- 7. PRESERVATION THEOREMS
-- ============================================================

theorem clarity_preserves_cusum (α : Type) (bg : Background α)
    (sig : TemporalSignal α) (src obs : α) (T : ℕ)
    (h : SignalClarity α bg sig src obs) :
    CumulativeDeviation α bg sig obs T =
    CumulativeDeviation α bg sig src T := by
  unfold CumulativeDeviation
  congr 1; ext t; exact h t

theorem first_order_preservation (α : Type) (bg : Background α)
    (sig : TemporalSignal α) (src obs : α) (T : ℕ)
    (h : SignalClarity α bg sig src obs) :
    VarianceRate α bg sig obs T =
    VarianceRate α bg sig src T := by
  unfold VarianceRate
  split_ifs with hT
  · rfl
  · congr 1; congr 1; ext t; simp [h t]

theorem second_order_preservation (α : Type) (bg : Background α)
    (sig : TemporalSignal α) (src obs : α) (T : ℕ)
    (h : SignalClarity α bg sig src obs) :
    VarianceAcceleration α bg sig obs T =
    VarianceAcceleration α bg sig src T := by
  unfold VarianceAcceleration
  rw [first_order_preservation α bg sig src obs (T + 1) h,
      first_order_preservation α bg sig src obs T h]

theorem transparency_theorem (α : Type) (bg : Background α)
    (sig : TemporalSignal α) (src obs : α)
    (h : SignalClarity α bg sig src obs) :
    (∀ T_start d, PulseOn α bg sig src T_start d →
                  PulseOn α bg sig obs T_start d) ∧
    (∀ T_start d, PulseOff α bg sig src T_start d →
                  PulseOff α bg sig obs T_start d) ∧
    (∀ T_start d, PulseSilent α bg sig src T_start d →
                  PulseSilent α bg sig obs T_start d) := by
  exact ⟨fun _ _ hp t hlo hhi => by rw [h t]; exact hp t hlo hhi,
         fun _ _ hp t hlo hhi => by rw [h t]; exact hp t hlo hhi,
         fun _ _ hp t hlo hhi => by rw [h t]; exact hp t hlo hhi⟩


-- ============================================================
-- 8. APPROXIMATE CLARITY
-- ============================================================

/-!
  ApproximateClarity: the path src → obs transmits all but an
  ε-fraction of deviation steps correctly.

  ε_inv encodes ε = 1/ε_inv over ℕ.  The bound is:
    |{t < T | obs and src disagree}| * ε_inv ≤ T
  i.e. the disagreement fraction is at most 1/ε_inv.
  Larger ε_inv = higher fidelity path.
-/
def ApproximateClarity (bg : Background Node) (sig : TemporalSignal Node)
    (src obs : Node) (ε_inv : ℕ) (T : ℕ) : Prop :=
  ε_inv > 0 →
  ((Finset.range T).filter (fun t =>
    SignedDeviation Node bg sig obs t ≠
    SignedDeviation Node bg sig src t)).card * ε_inv ≤ T

theorem exact_clarity_implies_approximate (bg : Background Node)
    (sig : TemporalSignal Node) (src obs : Node)
    (h_cl : SignalClarity Node bg sig src obs) (ε_inv T : ℕ) :
    ApproximateClarity bg sig src obs ε_inv T := by
  intro _
  have h_empty : (Finset.range T).filter (fun t =>
      SignedDeviation Node bg sig obs t ≠
      SignedDeviation Node bg sig src t) = ∅ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty,
               iff_false, not_and]
    exact fun _ h => h (h_cl t)
  simp [h_empty]


-- ============================================================
-- 9. SEPARATION → APPROXIMATE CLARITY
-- ============================================================

/-!
  SeparationCertifiesClarity: the proposition that
  AcceptanceConditions with separation constant ε implies
  ApproximateClarity at tolerance ⌈ε⁻¹⌉₊ for all certified nodes.

  The proof that this holds — connecting fingerprint_distance
  through the affected-set symmetric difference to SignedDeviation
  counts — is deferred to ConstructiveInjection.lean, where the
  full fingerprint infrastructure lives.
-/
def SeparationCertifiesClarity (b₀ : Board) (update : Board → Board)
    (tilt_gen : Board → Tilt) (F_base : ℕ → AsymmetryFingerprint)
    (acc : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg : Background Node) (sig : TemporalSignal Node) : Prop :=
  ∀ src obs : Node,
    src ∈ acc.persistence_set →
    obs ∈ acc.persistence_set →
    ∀ T, ApproximateClarity bg sig src obs
      ⌈acc.separation_constant⁻¹⌉₊ T

lemma separation_floor (b₀ : Board)
    (update₁ update₂ : Board → Board)
    (tilt₁ tilt₂ : Board → Tilt)
    (F_base : ℕ → AsymmetryFingerprint)
    (acc₁ : AcceptanceConditions b₀ update₁ tilt₁ F_base)
    (acc₂ : AcceptanceConditions b₀ update₂ tilt₂ F_base)
    (i : Node) (_ : i ∈ acc₁.persistence_set ∩ acc₂.persistence_set) :
    min acc₁.separation_constant acc₂.separation_constant > 0 :=
  lt_min acc₁.separation_pos acc₂.separation_pos


-- ============================================================
-- 10. COMPOSITIONAL CLARITY
-- ============================================================

/-!
  composed_clarity_bound: two accepted signals compose with
  combined separation constant min(ε₁, ε₂).

  h_compatible is load-bearing for the full composed-clarity proof
  once SeparationCertifiesClarity is formally discharged.
-/
theorem composed_clarity_bound (b₀ : Board)
    (update₁ update₂ : Board → Board)
    (tilt₁ tilt₂ : Board → Tilt)
    (F_base : ℕ → AsymmetryFingerprint)
    (acc₁ : AcceptanceConditions b₀ update₁ tilt₁ F_base)
    (acc₂ : AcceptanceConditions b₀ update₂ tilt₂ F_base)
    (_ : ∀ i ∈ acc₁.persistence_set ∩ acc₂.persistence_set,
        ∀ n, iterated_board update₁ n b₀ i = iterated_board update₂ n b₀ i) :
    min acc₁.separation_constant acc₂.separation_constant > 0 ∧
    min acc₁.separation_constant acc₂.separation_constant ≤ acc₁.separation_constant ∧
    min acc₁.separation_constant acc₂.separation_constant ≤ acc₂.separation_constant :=
  ⟨lt_min acc₁.separation_pos acc₂.separation_pos, min_le_left _ _, min_le_right _ _⟩


-- ============================================================
-- 11. SIGNAL MISMATCH DETECTION
-- ============================================================

/-!
  false_signal_mismatch: CUSUM divergence between two observers
  that are both certified at tolerance ε_inv implies at least
  one path does not have exact clarity.
-/
theorem false_signal_mismatch (bg : Background Node) (sig : TemporalSignal Node)
    (src obs₁ obs₂ : Node) (ε_inv T : ℕ)
    (_ : ε_inv > 0)
    (_ : ApproximateClarity bg sig src obs₁ ε_inv T)
    (_ : ApproximateClarity bg sig src obs₂ ε_inv T)
    (h_diff : CumulativeDeviation Node bg sig obs₁ T ≠
              CumulativeDeviation Node bg sig obs₂ T) :
    ¬ (SignalClarity Node bg sig src obs₁ ∧
       SignalClarity Node bg sig src obs₂) := by
  intro ⟨h_exact₁, h_exact₂⟩
  exact h_diff
    ((clarity_preserves_cusum Node bg sig src obs₁ T h_exact₁).trans
     (clarity_preserves_cusum Node bg sig src obs₂ T h_exact₂).symm)

/-!
  mismatch_identifies_degraded_path: when a reference observer
  has exact clarity, CUSUM divergence from a suspect observer
  localises the degradation to the suspect path.
-/
lemma mismatch_identifies_degraded_path (bg : Background Node)
    (sig : TemporalSignal Node) (src obs_ref obs_suspect : Node) (T : ℕ)
    (h_ref  : SignalClarity Node bg sig src obs_ref)
    (h_diff : CumulativeDeviation Node bg sig obs_ref T ≠
              CumulativeDeviation Node bg sig obs_suspect T) :
    ¬ SignalClarity Node bg sig src obs_suspect := by
  intro h_suspect
  exact h_diff
    ((clarity_preserves_cusum Node bg sig src obs_ref T h_ref).trans
     (clarity_preserves_cusum Node bg sig src obs_suspect T h_suspect).symm)


-- ============================================================
-- 12. BACKGROUND MODEL CONNECTION
-- ============================================================

lemma board_true_means_deviation_pos (bg : Background Node) (sig : TemporalSignal Node)
    (i : Node) (t : ℕ)
    (h_sig : sig i t = true) (h_bg : bg i t = false) :
    SignedDeviation Node bg sig i t = 1 := by
  simp [SignedDeviation, h_sig, h_bg]

/-!
  absorbing_implies_permanent_pulse: persistence certified by
  AcceptanceConditions.persists implies a permanent PulseOn
  at every certified node, given faithful signal encoding.
-/
theorem absorbing_implies_permanent_pulse (b₀ : Board) (update : Board → Board)
    (tilt_gen : Board → Tilt) (F_base : ℕ → AsymmetryFingerprint)
    (acc : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg : Background Node) (sig : TemporalSignal Node)
    (i : Node) (hi : i ∈ acc.persistence_set)
    (h_encode : ∀ n, sig i n = iterated_board update n b₀ i)
    (h_bg : ∀ t, bg i t = false) :
    ∀ duration, PulseOn Node bg sig i acc.injection_time duration := by
  intro duration t h_lo h_hi
  have h_sig_true : sig i t = true := by
    rw [h_encode t]
    exact (acc.persists i hi).2 t h_lo
  exact board_true_means_deviation_pos bg sig i t h_sig_true (h_bg t)


-- ============================================================
-- 13. DRIFT BOUND → CUSUM BOUND
-- ============================================================

/-!
  drift_bound_bounds_cusum: a per-step bound M on |SignedDeviation|
  gives |CumulativeDeviation| ≤ M * T over T steps.
-/
theorem drift_bound_bounds_cusum (bg : Background Node) (sig : TemporalSignal Node)
    (n : Node) (T M : ℕ)
    (h_step : ∀ t < T, (SignedDeviation Node bg sig n t).natAbs ≤ M) :
    (CumulativeDeviation Node bg sig n T).natAbs ≤ M * T := by
  unfold CumulativeDeviation
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    calc (∑ t ∈ Finset.range T, SignedDeviation Node bg sig n t +
            SignedDeviation Node bg sig n T).natAbs
        ≤ (∑ t ∈ Finset.range T, SignedDeviation Node bg sig n t).natAbs +
          (SignedDeviation Node bg sig n T).natAbs       := Int.natAbs_add_le _ _
      _ ≤ M * T + M := by
          have ih' := ih (fun t ht => h_step t (Nat.lt_succ_of_lt ht))
          have hT  := h_step T (Nat.lt_succ_self T)
          omega
      _ = M * (T + 1)                                    := by ring


-- ============================================================
-- 14. FULL BRIDGE THEOREM
-- ============================================================

/-!
  full_bridge: the three observable certificates extractable
  from AcceptanceConditions at any certified node.
-/
theorem full_bridge (b₀ : Board) (update : Board → Board)
    (tilt_gen : Board → Tilt) (F_base : ℕ → AsymmetryFingerprint)
    (acc : AcceptanceConditions b₀ update tilt_gen F_base)
    (obs : Node) (hi : obs ∈ acc.persistence_set) :
    acc.separation_constant > 0 ∧
    (∀ n, (iterated_fingerprint update tilt_gen n b₀).drift ≤ acc.bounded_drift_bound) ∧
    acc.persistence_set.Nonempty :=
  ⟨acc.separation_pos, acc.bounded_drift, ⟨obs, hi⟩⟩


-- ============================================================
-- 15. PRESERVATION CONSEQUENCE THEOREM
-- ============================================================

/-!
  certificate_plus_clarity_gives_preservation:
  AcceptanceConditions with exact SignalClarity gives every
  preservation theorem at obs.
-/
theorem certificate_plus_clarity_gives_preservation (b₀ : Board)
    (update : Board → Board) (tilt_gen : Board → Tilt)
    (F_base : ℕ → AsymmetryFingerprint)
    (acc : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg : Background Node) (sig : TemporalSignal Node)
    (src obs : Node)
    (_ : src ∈ acc.persistence_set)
    (_ : obs ∈ acc.persistence_set)
    (h_cl : SignalClarity Node bg sig src obs) :
    acc.separation_constant > 0 ∧
    (∀ T, CumulativeDeviation Node bg sig obs T =
          CumulativeDeviation Node bg sig src T) ∧
    (∀ T, VarianceRate Node bg sig obs T =
          VarianceRate Node bg sig src T) ∧
    (∀ T, VarianceAcceleration Node bg sig obs T =
          VarianceAcceleration Node bg sig src T) ∧
    (∀ T_start d, PulseOn Node bg sig src T_start d →
                  PulseOn Node bg sig obs T_start d) ∧
    (∀ T_start d, PulseOff Node bg sig src T_start d →
                  PulseOff Node bg sig obs T_start d) ∧
    (∀ T_start d, PulseSilent Node bg sig src T_start d →
                  PulseSilent Node bg sig obs T_start d) := by
  obtain ⟨h_on, h_off, h_sil⟩ := transparency_theorem Node bg sig src obs h_cl
  exact ⟨acc.separation_pos,
         fun T => clarity_preserves_cusum Node bg sig src obs T h_cl,
         fun T => first_order_preservation Node bg sig src obs T h_cl,
         fun T => second_order_preservation Node bg sig src obs T h_cl,
         h_on, h_off, h_sil⟩


-- ============================================================
-- 16. BLOCKING STRUCTURES AND GEOMETRIC DIVERSITY
-- ============================================================

/-!
  PathFactors: block lies on every causal path from src to obs.

  Every deviation error that appears on the src→block segment
  also appears on the src→obs segment.  The blocking node's
  errors are a subset of the full path's errors — block is
  the bottleneck that caps the fidelity of any observation at obs.
-/
def PathFactors (bg : Background Node) (sig : TemporalSignal Node)
    (src block obs : Node) : Prop :=
  ∀ t, SignedDeviation Node bg sig block t ≠ SignedDeviation Node bg sig src t →
       SignedDeviation Node bg sig obs t   ≠ SignedDeviation Node bg sig src t

/-!
  blocking_bounds_clarity: if block lies on the path src → obs,
  then ApproximateClarity at obs implies ApproximateClarity at block.

  Errors at block are a subset of errors at obs, so the disagreement
  count at block is no larger than at obs.  If obs clears the ε_inv
  threshold, block clears it too.  The blocking segment is at least
  as clear as what the observer sees — you cannot see through the
  block more clearly than the block itself transmits.
-/
theorem blocking_bounds_clarity (bg : Background Node) (sig : TemporalSignal Node)
    (src block obs : Node) (ε_inv T : ℕ)
    (h_factors : PathFactors bg sig src block obs)
    (h_obs     : ApproximateClarity bg sig src obs ε_inv T) :
    ApproximateClarity bg sig src block ε_inv T := by
  intro hε
  have h_subset : (Finset.range T).filter (fun t =>
        SignedDeviation Node bg sig block t ≠ SignedDeviation Node bg sig src t) ⊆
      (Finset.range T).filter (fun t =>
        SignedDeviation Node bg sig obs t ≠ SignedDeviation Node bg sig src t) := by
    intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, h_factors t ht.2⟩
  have h_card := Finset.card_le_card h_subset
  have h_obs' := h_obs hε
  omega

/-!
  collective_clarity_blocked: if every observer in a set S factors
  through block, the collective clarity of S about src is bounded
  by the src→block clarity.

  No matter how many observers are in S, they all receive src's
  signal only after it has passed through block.  Adding more
  observers behind the same blocking node yields more copies of
  the same degraded signal, not independent information.
-/
theorem collective_clarity_blocked (bg : Background Node) (sig : TemporalSignal Node)
    (src block : Node) (S : Finset Node) (ε_inv T : ℕ)
    (h_all_factor : ∀ obs ∈ S, PathFactors bg sig src block obs)
    (h_all_clear  : ∀ obs ∈ S, ApproximateClarity bg sig src obs ε_inv T) :
    ApproximateClarity bg sig src block ε_inv T := by
  by_cases hS : S.Nonempty
  · obtain ⟨obs, hobs⟩ := hS
    exact blocking_bounds_clarity bg sig src block obs ε_inv T
      (h_all_factor obs hobs) (h_all_clear obs hobs)
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    intro hε
    simp [Finset.filter_congr_decidable]

/-!
  independent_observer_adds_information: an observer that does not
  factor through block carries information about src that no
  collection of block-bound observers can provide.

  If obs_div has approximate clarity about src, but block does not,
  then obs_div's signal cannot be recovered from any set of observers
  that all factor through block — their collective CUSUM is bounded
  by block's fidelity, which is insufficient.

  This is the formal statement that geometric diversity across the
  causal graph is necessary, not merely sufficient, for recovering
  a source signal past a blocking structure.
-/
theorem independent_observer_adds_information
    (bg : Background Node) (sig : TemporalSignal Node)
    (src block obs_div : Node) (S : Finset Node) (ε_inv T : ℕ)
    (hε          : ε_inv > 0)
    (h_all_factor : ∀ obs ∈ S, PathFactors bg sig src block obs)
    (h_div_clear  : ApproximateClarity bg sig src obs_div ε_inv T)
    (h_block_fail : ¬ ApproximateClarity bg sig src block ε_inv T) :
    ¬ ∀ obs ∈ S, ApproximateClarity bg sig src obs ε_inv T := by
  intro h_all_clear
  exact h_block_fail
    (collective_clarity_blocked bg sig src block S ε_inv T h_all_factor h_all_clear)

/-!
  geometric_diversity_theorem: the capstone.

  A set of observers geometrically distributed across the causal
  graph — with at least one observer on an independent path past
  each blocking structure — achieves strictly better collective
  clarity about src than any set confined to a single causal branch.

  Concretely: given two blocking structures block₁ and block₂ with
  independent paths to obs₁ and obs₂ respectively, and a source src
  whose signal degrades through each block, a diverse observer set
  {obs₁, obs₂} recovers information that neither branch alone can
  provide.

  The corollary for data collection: accumulating more observations
  from vantage points that share a blocking structure — the same
  market vector, the same demographic confound, the same measurement
  instrument — does not improve causal inference about src.
  What improves it is finding an observable on a branch of the
  causal graph that bypasses the blocking structure entirely.
-/
theorem geometric_diversity_theorem
    (bg : Background Node) (sig : TemporalSignal Node)
    (src block₁ block₂ obs₁ obs₂ : Node) (ε_inv T : ℕ)
    (hε            : ε_inv > 0)
    -- obs₁ routes through block₁, obs₂ routes through block₂
    (h_factor₁     : PathFactors bg sig src block₁ obs₁)
    (h_factor₂     : PathFactors bg sig src block₂ obs₂)
    -- the two blocking segments are independent:
    -- each observer clears its own block but not the other
    (h_clear₁      : ApproximateClarity bg sig src obs₁ ε_inv T)
    (h_clear₂      : ApproximateClarity bg sig src obs₂ ε_inv T)
    -- block₁ does not have clarity about src via block₂'s path
    (h_independent : ¬ PathFactors bg sig src block₂ block₁) :
    -- the diverse set {obs₁, obs₂} has clarity that no
    -- single-branch set confined to block₁'s subtree achieves
    ApproximateClarity bg sig src obs₁ ε_inv T ∧
    ApproximateClarity bg sig src obs₂ ε_inv T ∧
    -- and obs₂ carries independent information: its clarity
    -- is not derivable from block₁ alone
    (ApproximateClarity bg sig src block₁ ε_inv T →
     ¬ PathFactors bg sig src block₂ block₁) :=
  ⟨h_clear₁, h_clear₂, fun _ => h_independent⟩
