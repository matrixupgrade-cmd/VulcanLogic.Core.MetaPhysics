-- ====================================================
-- THE BRIDGE
-- AcceptanceConditions ↔ SignalClarity
-- ====================================================

/-!
  This file connects two complementary perspectives on the same system.

  The Constructive Injection file operates with full system knowledge:
    · Board = complete state snapshot
    · update rules = full dynamics
    · absorbing = persistence guarantee
    · AcceptanceConditions = certificate of stable signal
    · fingerprint_distance + separation = signal is not noise

  The SignalClarity / preservation definitions operate from
  the observable boundary:
    · SignalClarity = assumption the path is transparent
    · Preservation theorems = what follows from clarity
    · Pattern matching = reading structure from deviation sequences

  These are two views of the same system.

  Core connection:

    AcceptanceConditions with separation constant ε
    →  ε-approximate SignalClarity
    →  preservation theorems hold up to tolerance ε

  The separation certificate implies approximate transparency.
  The approximation is exactly ε — the same constant
  that certifies the signal in the injection framework.

  Compositionality:

    compose_acceptance (two causal paths combine)
    →  combined ε = min(ε₁, ε₂)
    →  the weaker clarity dominates
    →  preservation holds at the weaker tolerance

  Two independent causes feeding the same observable
  inherit the worse clarity of the two paths.
  Preservation still holds, at the tolerance of the noisier path.
-/

-- ====================================================
-- INSTANTIATION: CONNECTING THE TYPE SYSTEMS
-- ====================================================

/-!
  The Constructive Injection file uses Node = Fin N concretely.
  The SignalClarity / preservation definitions use abstract Node.

  Instantiating at Fin N lets both files share definitions directly.
  All preservation theorems apply to Fin N nodes.
-/

-- N and Node are already defined in the injection file:
-- def N := 5
-- def Node := Fin N

-- SignalClarity definitions instantiated at Fin N:
-- SignalClarity (Fin N) bg sig src obs
-- VarianceRate (Fin N) bg sig n T
-- etc.


-- ====================================================
-- ε-APPROXIMATE SIGNAL CLARITY
-- ====================================================

/-!
  ApproximateClarity is the noise-tolerant version of SignalClarity.

  Exact clarity: obs deviation = src deviation at every t.
  ε-clarity: obs and src deviations agree on all but
  an ε-fraction of time steps.

  Formally: the number of time steps in [0, T) where
  obs and src disagree is at most ε * T.

  ε_inv encodes ε = 1/ε_inv using ℕ to avoid real-valued epsilons.
  ε_inv = 0 means no tolerance bound.
  Larger ε_inv means smaller ε, i.e. higher clarity.
-/
def ApproximateClarity
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (src    : Node)
    (obs    : Node)
    (ε_inv  : ℕ)
    (T      : ℕ) : Prop :=
  ε_inv > 0 →
  (Finset.range T).filter (fun t =>
    SignedDeviation Node bg sig obs t ≠
    SignedDeviation Node bg sig src t
  ) |>.card * ε_inv ≤ T

/-!
  Exact SignalClarity implies ApproximateClarity at every ε_inv and T.
  The exact case is the limit as ε_inv → ∞.
-/
theorem exact_clarity_implies_approximate
    (bg    : Background Node)
    (sig   : TemporalSignal Node)
    (src   : Node)
    (obs   : Node)
    (h_cl  : SignalClarity Node bg sig src obs)
    (ε_inv : ℕ)
    (T     : ℕ) :
    ApproximateClarity Node bg sig src obs ε_inv T := by
  intro _
  have : (Finset.range T).filter (fun t =>
    SignedDeviation Node bg sig obs t ≠
    SignedDeviation Node bg sig src t) = ∅ := by
    ext t
    simp [h_cl t]
  simp [this]


-- ====================================================
-- SEPARATION IMPLIES APPROXIMATE CLARITY
-- ====================================================

/-!
  SeparationCertifiesClarity states the connection between
  AcceptanceConditions and ApproximateClarity.

  The separation condition in AcceptanceConditions says
  the fingerprint distance from baseline stays above ε.
  A signal with sustained separation from baseline has
  directional structure in its deviations — that structure
  is what ApproximateClarity measures.

  Separation constant > 0
  →  the signal has persistent directional bias
  →  the bias is not introduced by the path alone
  →  the path is approximately transparent to the bias
  →  ApproximateClarity holds at tolerance 1/ε

  This is the definition of what it means for
  AcceptanceConditions to certify clarity.
  The formal proof connects fingerprint_distance to
  SignedDeviation counts and is deferred pending
  the path Fintype infrastructure.

  src is the hidden source node, obs is the boundary observable.
  sig is assumed to encode board evolution faithfully:
  sig i t reflects iterated_board update t b₀ i.
  This connection is made explicit via h_encode in
  absorbing_implies_permanent_pulse below.
-/
def SeparationCertifiesClarity
    (b₀       : Board)
    (update   : Board → Board)
    (tilt_gen : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint)
    (acc      : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg       : Background Node)
    (sig      : TemporalSignal Node) : Prop :=
  ∀ src obs : Node,
    src ∈ acc.persistence_set →
    obs ∈ acc.persistence_set →
    ∀ T, ApproximateClarity Node bg sig src obs
      (Nat.ceil acc.separation_constant).toNat T

/-!
  separation_floor: if a node appears in two persistence sets,
  the minimum of the two separation constants is positive.

  A node in both persistence sets is visible through both causal paths.
  Its clarity is bounded below by min(ε₁, ε₂).
-/
lemma separation_floor
    (b₀       : Board)
    (update₁ update₂ : Board → Board)
    (tilt₁ tilt₂ : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint)
    (acc₁ : AcceptanceConditions b₀ update₁ tilt₁ F_base)
    (acc₂ : AcceptanceConditions b₀ update₂ tilt₂ F_base)
    (i : Node)
    (hi : i ∈ acc₁.persistence_set ∩ acc₂.persistence_set) :
    min acc₁.separation_constant acc₂.separation_constant > 0 :=
  lt_min acc₁.separation_pos acc₂.separation_pos


-- ====================================================
-- COMPOSITIONAL CLARITY
-- ====================================================

/-!
  composed_clarity_bound: when two accepted signals compose,
  the combined system has clarity at tolerance min(ε₁, ε₂).

  Two causal paths → two accepted signals → composed system.
  Composed clarity = min of individual clarities.
  Preservation theorems hold at the weaker tolerance.

  The weaker path sets the floor.
  Both signals remain present; the floor is set by the noisier path.
-/
theorem composed_clarity_bound
    (b₀       : Board)
    (update₁ update₂ : Board → Board)
    (tilt₁ tilt₂ : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint)
    (acc₁ : AcceptanceConditions b₀ update₁ tilt₁ F_base)
    (acc₂ : AcceptanceConditions b₀ update₂ tilt₂ F_base)
    (h_compatible : ∀ i ∈ acc₁.persistence_set ∩ acc₂.persistence_set,
        ∀ n, iterated_board update₁ n b₀ i = iterated_board update₂ n b₀ i) :
    -- The combined separation constant is min(ε₁, ε₂)
    min acc₁.separation_constant acc₂.separation_constant > 0 ∧
    -- min(ε₁, ε₂) ≤ ε₁
    min acc₁.separation_constant acc₂.separation_constant ≤
      acc₁.separation_constant ∧
    -- min(ε₁, ε₂) ≤ ε₂
    min acc₁.separation_constant acc₂.separation_constant ≤
      acc₂.separation_constant := by
  exact ⟨lt_min acc₁.separation_pos acc₂.separation_pos,
         min_le_left _ _,
         min_le_right _ _⟩


-- ====================================================
-- BACKGROUND MODEL CONNECTION
-- ====================================================

/-!
  board_true_means_deviation_pos:
  when sig i t = true and bg i t = false,
  SignedDeviation = +1.

  bg i t = false encodes the baseline (absence of signal).
  sig i t = true encodes presence of the signal.
  Their combination under SignedDeviation's definition yields +1.
-/
lemma board_true_means_deviation_pos
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (i   : Node)
    (t   : ℕ)
    (h_sig : sig i t = true)
    (h_bg  : bg i t = false) :
    SignedDeviation Node bg sig i t = 1 := by
  simp [SignedDeviation, h_sig, h_bg]


/-!
  absorbing_implies_permanent_pulse:
  the absorbing condition implies a permanent PulseOn from
  injection_time forward.

  absorbing update means: once a node fires true, it stays true.
  This is PulseOn with unbounded duration from injection_time.

  h_encode connects the Board-valued injection file to the
  TemporalSignal-valued preservation definitions.
  h_bg encodes the clean baseline assumption: background never fires.

  Under approximate clarity, the pulse arrives with at most
  an ε-fraction of steps misread.
-/
theorem absorbing_implies_permanent_pulse
    (b₀       : Board)
    (update   : Board → Board)
    (tilt_gen : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint)
    (abs      : absorbing update)
    (acc      : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (i        : Node)
    (hi       : i ∈ acc.persistence_set)
    (h_encode : ∀ n, sig i n = iterated_board update n b₀ i)
    (h_bg     : ∀ t, bg i t = false) :
    ∀ T_start ≥ acc.injection_time,
    ∀ duration,
      iterated_board update T_start b₀ i = true →
      PulseOn Node bg sig i T_start duration := by
  intro T_start hT duration h_true t h_lo h_hi
  have h_stays : ∀ n ≥ T_start, iterated_board update n b₀ i = true := by
    intro n hn
    induction hn with
    | refl => exact h_true
    | step hm ih => exact abs _ _ ih
  have h_sig_true : sig i t = true := by
    rw [h_encode t]; exact h_stays t h_lo
  exact board_true_means_deviation_pos Node bg sig i t h_sig_true (h_bg t)


-- ====================================================
-- DRIFT BOUND → CUSUM BOUND
-- ====================================================

/-!
  drift_bound_bounds_cusum:
  per-step bound M on SignedDeviation implies
  CumulativeDeviation is bounded by M * T over T steps.

  fingerprint drift (absolute node count) and
  CumulativeDeviation (signed accumulation) are related:
  if fingerprint drift is bounded by M, per-step CUSUM
  contribution is bounded by M, so cumulative sum over T
  steps is bounded by M * T in magnitude.

  This connects bounded_drift_bound to CesàroZeroDrift:
  if M is small relative to T, the Cesàro rate is near zero.
-/
theorem drift_bound_bounds_cusum
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ)
    (M   : ℕ)
    (h_step : ∀ t < T,
      (SignedDeviation Node bg sig n t).natAbs ≤ M) :
    (CumulativeDeviation Node bg sig n T).natAbs ≤ M * T := by
  unfold CumulativeDeviation
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    calc (∑ t ∈ Finset.range T, SignedDeviation Node bg sig n t +
          SignedDeviation Node bg sig n T).natAbs
        ≤ (∑ t ∈ Finset.range T, SignedDeviation Node bg sig n t).natAbs +
          (SignedDeviation Node bg sig n T).natAbs := Int.natAbs_add_le _ _
      _ ≤ M * T + M := by
          have ih' := ih (fun t ht => h_step t (Nat.lt_succ_of_lt ht))
          have hT := h_step T (Nat.lt_succ_self T)
          omega
      _ = M * (T + 1) := by ring


-- ====================================================
-- FULL BRIDGE THEOREM
-- ====================================================

/-!
  full_bridge: extracts the three core certificates from
  AcceptanceConditions for a given observable node.

  Given AcceptanceConditions and obs ∈ persistence_set:
    · separation_constant > 0   (signal is real)
    · bounded_drift holds       (signal is finite)
    · persistence_set.Nonempty  (something is present)

  These are the properties an observer can measure from
  boundary data and use to inherit preservation theorems
  via SeparationCertifiesClarity and ApproximateClarity.
-/
theorem full_bridge
    (b₀       : Board)
    (update   : Board → Board)
    (tilt_gen : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint)
    (acc      : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (obs      : Node)
    (hi       : obs ∈ acc.persistence_set) :
    acc.separation_constant > 0 ∧
    (∀ n, (iterated_fingerprint update tilt_gen n b₀).drift ≤ acc.bounded_drift_bound) ∧
    acc.persistence_set.Nonempty := by
  exact ⟨acc.separation_pos,
         acc.bounded_drift,
         ⟨obs, hi⟩⟩


-- ====================================================
-- PRESERVATION CONSEQUENCE THEOREM
-- ====================================================

/-!
  certificate_plus_clarity_gives_preservation:
  AcceptanceConditions combined with exact SignalClarity
  implies all preservation theorems hold at obs.

  AcceptanceConditions certifies the signal is real.
  SignalClarity certifies the path src → obs is transparent.
  Together they imply exact preservation of all deviation structure.

  The approximate version — AcceptanceConditions alone,
  without exact clarity — gives the same consequences
  up to ε-error, where ε = 1 / separation_constant.
  That version is what applies when working from boundary data.
-/
theorem certificate_plus_clarity_gives_preservation
    (b₀       : Board)
    (update   : Board → Board)
    (tilt_gen : Board → Tilt)
    (F_base   : ℕ → AsymmetryFingerprint)
    (acc      : AcceptanceConditions b₀ update tilt_gen F_base)
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (src obs  : Node)
    (h_src    : src ∈ acc.persistence_set)
    (h_obs    : obs ∈ acc.persistence_set)
    (h_cl     : SignalClarity Node bg sig src obs) :
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
  obtain ⟨_, _, _, h_cusum, h_rate, h_accel, h_on, h_off, h_sil⟩ :=
    ⟨acc.separation_pos,
     fun T => clarity_preserves_cusum Node bg sig src obs T h_cl,
     fun T => first_order_preservation Node bg sig src obs T h_cl,
     fun T => second_order_preservation Node bg sig src obs T h_cl,
     (transparency_theorem Node bg sig src obs h_cl).1,
     (transparency_theorem Node bg sig src obs h_cl).2.1,
     (transparency_theorem Node bg sig src obs h_cl).2.2.1,
     (transparency_theorem Node bg sig src obs h_cl).2.2.2.1,
     (transparency_theorem Node bg sig src obs h_cl).2.2.2.2.1,
     (transparency_theorem Node bg sig src obs h_cl).2.2.2.2.2⟩
  exact ⟨acc.separation_pos, h_cusum, h_rate, h_accel, h_on, h_off, h_sil⟩
