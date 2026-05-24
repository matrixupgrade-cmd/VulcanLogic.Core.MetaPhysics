-- ====================================================
-- LAYER 14: SIGNAL CLARITY AND RATE-OF-CHANGE PRESERVATION
-- ====================================================

/-!
  THE CORE ASSUMPTION OF THIS LAYER.

  Real causal chains are messy. Hidden nodes add variance.
  Transfer functions distort. Bottlenecks blur timing.
  Intermediate structure whitewashes signal texture.

  All of that complexity is REAL — and deliberately
  deferred to applied files where empirical filtering
  belongs.

  This layer asks a simpler question:

    IF signal clarity holds —
    IF the path from hidden structure to observer
       adds no intrinsic variance of its own —
    WHAT is then guaranteed at the observable boundary?

  The answer: EVERYTHING is preserved.
  Not just the presence of a signal (Layer 11).
  Not just the drift (CUSUM).
  But the SHAPE — the rate of change, the acceleration
  of variance, the on/off pulse timing.

  The hidden causal structure arrives at the observer
  undistorted. Measuring variance at the boundary
  IS measuring variance in the hidden structure.

  This is the cleanest possible case.
  Real systems are dirtier. That is an empirical matter.
  This layer establishes what clarity MEANS and what
  it GUARANTEES — so the dirty cases can be understood
  as deviations from this ideal.

  WHAT SIGNAL CLARITY IS NOT:
    · It does not mean the signal is large
    · It does not mean the hidden structure is simple
    · It does not mean there is no noise at the boundary
    · It means: the path itself contributes zero
      additional variance structure
      The observer's variance = the source's variance

  THE THREE PRESERVATION THEOREMS:

    1. FIRST ORDER PRESERVATION
       Rate of change of variance at source =
       Rate of change of variance at observer.
       If the source is accelerating, the observer
       sees acceleration. If decelerating, deceleration.

    2. SECOND ORDER PRESERVATION
       The rate of change OF the rate of change preserves.
       Curvature of the variance trajectory is intact.
       The observer sees not just direction but texture.

    3. PULSE PATTERN PRESERVATION
       On/off timing — the Morse code structure —
       arrives undistorted.
       A switch in the hidden structure is a switch
       at the observer. The pause lengths are preserved.
       The burst durations are preserved.

  TOGETHER:
    Under signal clarity, the observable is a
    transparent window into the hidden causal structure.
    Pattern matching at the boundary is pattern matching
    in the hidden graph. The bobber moves because the
    fish moved — not because the water is choppy.

  DESIGN NOTE:
    Signal clarity is introduced as an axiom — a named
    assumption. The theorems are then conditional on it.
    This keeps combinatorial explosion out of this file.
    The "how to achieve clarity" question belongs to
    applied layers. The "what follows from clarity"
    question is answered here.
-/


-- ====================================================
-- SIGNAL CLARITY: THE AXIOMATIC ASSUMPTION
-- ====================================================

/-!
  SignalClarity is the assumption that the path from
  a source node src to an observer node obs contributes
  zero intrinsic variance of its own.

  Formally: for every time t, the signed deviation
  at obs equals the signed deviation at src.
  The path is the identity transform.

  This is stated as a Prop — a named hypothesis that
  theorems can assume. It is not claimed to hold in
  general. It is the condition under which the
  preservation theorems fire.

  NOTE ON SCOPE:
    SignalClarity is a pairwise condition between src
    and obs. A system can have clarity on some paths
    and not others. Theorems that use it are conditional
    on which paths have it.
-/
def SignalClarity
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (src : Node)
    (obs : Node) : Prop :=
  ∀ t : ℕ,
    SignedDeviation Node bg sig obs t =
    SignedDeviation Node bg sig src t

/-!
  CLARITY IS SYMMETRIC IN DEVIATION SPACE.

  If obs sees src's deviation faithfully,
  then any measurement at obs is a measurement at src.
  The nodes are indistinguishable to the CUSUM detector.

  This is the operational meaning of clarity:
  the observer and the source are the same node
  from the perspective of variance measurement.
-/
theorem clarity_deviation_identity
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (src : Node)
    (obs : Node)
    (t   : ℕ)
    (h   : SignalClarity Node bg sig src obs) :
    SignedDeviation Node bg sig obs t =
    SignedDeviation Node bg sig src t :=
  h t

/-!
  CLARITY PRESERVES CUMULATIVE DEVIATION.

  If signal clarity holds on src → obs,
  then CumulativeDeviation at obs equals
  CumulativeDeviation at src over any window T.

  The CUSUM at the boundary IS the CUSUM of the source.
  Drift detected at obs is drift present at src.
  No ambiguity about whether the path introduced the drift.
-/
theorem clarity_preserves_cusum
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (src : Node)
    (obs : Node)
    (T   : ℕ)
    (h   : SignalClarity Node bg sig src obs) :
    CumulativeDeviation Node bg sig obs T =
    CumulativeDeviation Node bg sig src T := by
  unfold CumulativeDeviation
  congr 1
  ext t
  exact h t


-- ====================================================
-- FIRST ORDER PRESERVATION
-- ====================================================

/-!
  Rate of change of variance — the discrete first
  derivative of CumulativeDeviation.

  VarianceRate at time T is the change in cumulative
  deviation between window T and window T+1.
  This equals SignedDeviation at time T — the
  instantaneous contribution of the new observation.

  It is the "velocity" of the cumulative signal.
  A high positive rate means the signal is actively
  deviating upward from background.
  A negative rate means active downward deviation.
  Zero means momentary alignment with background.
-/
def VarianceRate
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : ℤ :=
  CumulativeDeviation Node bg sig n (T + 1) -
  CumulativeDeviation Node bg sig n T

/-!
  VarianceRate equals SignedDeviation pointwise.
  The instantaneous rate is the instantaneous deviation.
  This is the fundamental identity connecting the
  cumulative (CUSUM) view to the instantaneous view.
-/
lemma variance_rate_eq_signed_deviation
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) :
    VarianceRate Node bg sig n T =
    SignedDeviation Node bg sig n T := by
  unfold VarianceRate CumulativeDeviation
  simp [Finset.sum_range_succ]

/-!
  FIRST ORDER PRESERVATION THEOREM.

  Under signal clarity, the rate of variance change
  at the observer equals the rate at the source.

  If the source is actively deviating upward, the
  observer sees the same upward rate.
  If the source goes quiet, the observer goes quiet.

  The velocity of the signal is preserved exactly.
  No lag. No attenuation. No phase shift.

  This is what "no intrinsic path variance" means
  at the first-order level.
-/
theorem first_order_preservation
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (src : Node)
    (obs : Node)
    (T   : ℕ)
    (h   : SignalClarity Node bg sig src obs) :
    VarianceRate Node bg sig obs T =
    VarianceRate Node bg sig src T := by
  simp [variance_rate_eq_signed_deviation]
  exact h T


-- ====================================================
-- SECOND ORDER PRESERVATION
-- ====================================================

/-!
  Acceleration of variance — the discrete second
  derivative of CumulativeDeviation.

  VarianceAcceleration at time T is the change in
  VarianceRate between T and T+1.
  It measures whether the signal is speeding up or
  slowing down in its deviation from background.

  Positive acceleration: deviation is intensifying
  Negative acceleration: deviation is diminishing
  Zero: rate is steady (constant deviation velocity)

  This is the "curvature" of the variance trajectory.
  A signal that spikes and then decays has positive
  then negative acceleration — a shape, not just a level.
  Under clarity, that shape arrives at the observer intact.
-/
def VarianceAcceleration
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : ℤ :=
  VarianceRate Node bg sig n (T + 1) -
  VarianceRate Node bg sig n T

/-!
  SECOND ORDER PRESERVATION THEOREM.

  Under signal clarity, variance acceleration at
  the observer equals acceleration at the source.

  The curvature of the variance trajectory preserves.
  A spike that builds then fades in the hidden structure
  builds then fades at the observer with the same shape.

  This is what makes pattern matching meaningful:
  the observer is not seeing a blurred version of
  the source pattern. They are seeing the same pattern.
  The second derivative — the texture — is intact.

  Proof follows directly from first order preservation
  applied twice.
-/
theorem second_order_preservation
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (src : Node)
    (obs : Node)
    (T   : ℕ)
    (h   : SignalClarity Node bg sig src obs) :
    VarianceAcceleration Node bg sig obs T =
    VarianceAcceleration Node bg sig src T := by
  unfold VarianceAcceleration
  rw [first_order_preservation Node bg sig src obs (T + 1) h]
  rw [first_order_preservation Node bg sig src obs T h]


-- ====================================================
-- PULSE PATTERN PRESERVATION
-- ====================================================

/-!
  A PULSE is a contiguous window [T_start, T_end)
  during which the signal is consistently above or
  below background — a sustained on or off period.

  PulseOn: SignedDeviation = +1 throughout the window
  PulseOff: SignedDeviation = -1 throughout the window
  PulseSilent: SignedDeviation = 0 throughout the window

  These are the Morse code primitives:
    PulseOn     → dot or dash (active signal)
    PulseOff    → active suppression
    PulseSilent → gap between pulses

  The timing of these pulses — their start, duration,
  and sequence — is the pulse pattern.
  It encodes the on/off rhythm of the hidden structure.
-/
def PulseOn
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (n        : Node)
    (T_start  : ℕ)
    (duration : ℕ) : Prop :=
  ∀ t, T_start ≤ t → t < T_start + duration →
    SignedDeviation Node bg sig n t = 1

def PulseOff
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (n        : Node)
    (T_start  : ℕ)
    (duration : ℕ) : Prop :=
  ∀ t, T_start ≤ t → t < T_start + duration →
    SignedDeviation Node bg sig n t = -1

def PulseSilent
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (n        : Node)
    (T_start  : ℕ)
    (duration : ℕ) : Prop :=
  ∀ t, T_start ≤ t → t < T_start + duration →
    SignedDeviation Node bg sig n t = 0

/-!
  PULSE PATTERN PRESERVATION — ON PULSES.

  Under signal clarity, if the source has an active
  pulse (PulseOn) over window [T_start, T_start + d),
  then the observer has exactly the same active pulse
  over exactly the same window.

  The timing is identical. The duration is identical.
  The pulse does not smear, delay, or attenuate.

  This is the formal content of:
  "A switch in the hidden structure is a switch
   at the observer. The pause lengths preserve."
-/
theorem pulse_on_preservation
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (src      : Node)
    (obs      : Node)
    (T_start  : ℕ)
    (duration : ℕ)
    (h_cl     : SignalClarity Node bg sig src obs)
    (h_pulse  : PulseOn Node bg sig src T_start duration) :
    PulseOn Node bg sig obs T_start duration := by
  intro t h_lo h_hi
  rw [h_cl t]
  exact h_pulse t h_lo h_hi

/-!
  PULSE PATTERN PRESERVATION — OFF PULSES.

  Under signal clarity, suppression in the source
  is suppression at the observer.
  The active-low pattern preserves exactly.
-/
theorem pulse_off_preservation
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (src      : Node)
    (obs      : Node)
    (T_start  : ℕ)
    (duration : ℕ)
    (h_cl     : SignalClarity Node bg sig src obs)
    (h_pulse  : PulseOff Node bg sig src T_start duration) :
    PulseOff Node bg sig obs T_start duration := by
  intro t h_lo h_hi
  rw [h_cl t]
  exact h_pulse t h_lo h_hi

/-!
  PULSE PATTERN PRESERVATION — SILENT GAPS.

  Under signal clarity, silence in the source
  is silence at the observer.
  The gap structure — the pauses between pulses —
  preserves exactly.

  This matters because the gap duration is as
  diagnostic as the pulse duration. In Morse code,
  the space between dots and dashes carries meaning.
  Under clarity, that meaning arrives intact.
-/
theorem pulse_silent_preservation
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (src      : Node)
    (obs      : Node)
    (T_start  : ℕ)
    (duration : ℕ)
    (h_cl     : SignalClarity Node bg sig src obs)
    (h_pulse  : PulseSilent Node bg sig src T_start duration) :
    PulseSilent Node bg sig obs T_start duration := by
  intro t h_lo h_hi
  rw [h_cl t]
  exact h_pulse t h_lo h_hi


-- ====================================================
-- THE TRANSPARENCY THEOREM
-- ====================================================

/-!
  THE TRANSPARENCY THEOREM.

  The unifying result of this layer.

  Under signal clarity, the observer is a transparent
  window into the hidden causal structure.
  All three orders of variance structure preserve:

    1. Cumulative deviation (CUSUM) — the drift
    2. First order (VarianceRate) — the velocity
    3. Second order (VarianceAcceleration) — the texture
    4. Pulse patterns (on, off, silent) — the Morse code

  Measuring variance at obs IS measuring variance at src.
  The path between them is invisible to the measurement.

  WHAT THIS MEANS FOR PATTERN MATCHING:

  If the observer finds a wiggle pattern that matches
  a known causal signature — e.g. the UV seasonal pattern,
  the Parkinson's gut-switch pattern, the orbital wobble
  pattern — and signal clarity holds on that path, then
  the match is not an artifact of the transmission.

  The match is a match in the hidden structure itself.
  The observer is seeing the source, not a distortion of it.

  This is the formal justification for the fingerprinting
  logic introduced in the conversation:

    "I got this wiggle pattern and it matches with the
     causal pattern over here."

  Under clarity, that statement has mathematical content.
  The wiggle pattern IS the causal pattern.
  Not approximately. Exactly.

  REAL SYSTEMS:
  Real systems are not perfectly clear.
  Dirty paths are the norm.
  This theorem establishes the IDEAL — the baseline
  against which real systems are measured.
  An empirically close match to a known signature,
  on a path with measured low distortion, inherits
  the force of this theorem approximately.
  The formal machinery for "approximately" belongs
  to applied layers.
-/
theorem transparency_theorem
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (src : Node)
    (obs : Node)
    (h   : SignalClarity Node bg sig src obs) :
    -- CUSUM preserves
    (∀ T, CumulativeDeviation Node bg sig obs T =
          CumulativeDeviation Node bg sig src T) ∧
    -- First order preserves
    (∀ T, VarianceRate Node bg sig obs T =
          VarianceRate Node bg sig src T) ∧
    -- Second order preserves
    (∀ T, VarianceAcceleration Node bg sig obs T =
          VarianceAcceleration Node bg sig src T) ∧
    -- Pulse on preserves
    (∀ T_start d, PulseOn Node bg sig src T_start d →
                  PulseOn Node bg sig obs T_start d) ∧
    -- Pulse off preserves
    (∀ T_start d, PulseOff Node bg sig src T_start d →
                  PulseOff Node bg sig obs T_start d) ∧
    -- Pulse silent preserves
    (∀ T_start d, PulseSilent Node bg sig src T_start d →
                  PulseSilent Node bg sig obs T_start d) := by
  exact ⟨
    fun T   => clarity_preserves_cusum Node bg sig src obs T h,
    fun T   => first_order_preservation Node bg sig src obs T h,
    fun T   => second_order_preservation Node bg sig src obs T h,
    fun T d => pulse_on_preservation Node bg sig src obs T d h,
    fun T d => pulse_off_preservation Node bg sig src obs T d h,
    fun T d => pulse_silent_preservation Node bg sig src obs T d h
  ⟩


-- ====================================================
-- CONNECTION TO PREVIOUS LAYERS
-- ====================================================

/-!
  BRIDGE TO LAYER 11 (CUSUM / DRIFT DETECTION).

  Layer 11 says: persistent drift implies hidden structure.
  Layer 14 adds: under clarity, detected drift at obs
  IS the drift of src — not a path artifact.

  The CUSUM fires at obs.
  Without clarity: ambiguous — could be path variance.
  With clarity: unambiguous — the drift is in the source.

  clarity_preserves_cusum is the bridge theorem.
  It makes Layer 11's detection result attributable
  to the source rather than the path.

  BRIDGE TO LAYER 12 (POWERHOUSE / PATIENCE / SHERLOCK).

  The Sherlock conjecture says: complex sources produce
  unique patterns. Under clarity, the unique pattern
  arrives intact at the observer. The pattern matching
  that Sherlock relies on is exact, not approximate.

  Powerhouse + Clarity: high background entropy amplifies
  the contrast of a preserved signal. The quiet lake
  under clarity gives the cleanest possible fingerprint.

  BRIDGE TO LAYER 13 (COMPLEXITY IMPLIES UNIQUENESS).

  Layer 13 says: complex hidden graphs produce patterns
  that few other graphs can mimic. Under clarity, the
  observer sees that complex pattern exactly — the full
  second-order texture, the pulse timing, all of it.
  PatternComplexity is computed on the true source pattern,
  not a blurred version. Identification is maximally sharp.

  BRIDGE TO D₁ / COHERENT DELTA (Layer 9).

  D₁ catches sharp local events — spikes.
  Under clarity, a spike in the source is a spike at obs
  with identical timing and magnitude (in the ±1 encoding).
  PulseOn with duration = 1 is a single-point spike.
  pulse_on_preservation handles this as a special case.

  SUMMARY OF THE CLARITY GUARANTEE:

  Without clarity:
    Observer sees: source signal + path noise + distortion
    Detection: possible (CUSUM still fires)
    Attribution: ambiguous (path or source?)
    Pattern matching: approximate (shape may be distorted)

  With clarity:
    Observer sees: source signal exactly
    Detection: exact (CUSUM at obs = CUSUM at src)
    Attribution: unambiguous (obs IS src for measurement)
    Pattern matching: exact (shape fully preserved)

  Clarity does not make signals appear that aren't there.
  It makes signals that ARE there visible without distortion.
  The bobber in flat water gives a clean read.
  Clarity is flat water.
-/
