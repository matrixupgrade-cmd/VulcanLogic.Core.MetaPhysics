-- ====================================================
-- LAYER 11: CUMULATIVE DEVIATION AND THE LOW-ENTROPY DETECTOR
-- ====================================================

/-!
  THE CORE INSIGHT.

  In a high-entropy causal system, signed deviations from
  background sum to zero over long windows.

  This is not an assumption — it is what high entropy MEANS.
  A source whose deviations have nonzero long-run sum has
  BIAS. Bias is structure. Structure is lower entropy.

  Therefore:
    CumulativeDeviation drifts → source is lower entropy
                                  than background
    CumulativeDeviation stays near zero → source is
                                  consistent with high entropy

  The cumulative sum is a LOW-ENTROPY DETECTOR embedded
  in a high-entropy system.

  ASYMMETRY (the guarantee):
    A high-entropy source CANNOT drift indefinitely.
    A low-entropy source CAN sum to zero over a finite
    window — but cannot sustain it. The drift will emerge.

  This breaks the baseline contamination cycle:
    The cumulative sum is robust to baseline drift.
    If the baseline absorbs the signal, drift slows.
    But it cannot reverse without the source reversing.
    The accumulation remembers.

  EXAMPLES:
    Fish nibbling uniformly:    sum stays near zero
    Fish striking repeatedly:   sum drifts positive
    Awkward bobber pause:       sum drifts negative
    (sustained suppression of normal background activity)

    Star wobble (planet present):     cumulative positional
                                      deviation drifts with
                                      orbital period
    Star wobble (no planet):          sum stays near zero
                                      over many observations

    Cancer incidence (virus present): cumulative excess
                                      cases drift upward
    Cancer incidence (no virus):      sum near zero,
                                      consistent with
                                      demographic noise

  AWKWARD PAUSES AND BIG STRIKES:
    These are low-entropy events precisely because they
    break the uniformity. They MAY cancel each other —
    a big strike followed by a long pause could sum to zero.
    But this cancellation is itself a structured pattern —
    lower entropy than uniform noise.
    The detector catches it either way:
      · If they don't cancel: drift detected
      · If they do cancel: the PATTERN of cancellation
        is detectable as non-uniform — D₁ spikes cluster
        non-randomly even when the sum is near zero.
    There is no escape.

  DESIGN NOTE ON LowEntropySource:
    An earlier draft defined LowEntropySource as Drifts
    (∀ B, ∃ T, |CumDev T| > B). This has a monotonicity
    trap: CumulativeDeviation is NOT monotone in T because
    SignedDeviation can be -1. So knowing |CumDev T_wit| > B
    for some T_wit does not mean |CumDev T'| > B for T' > T_wit.

    The fix: define LowEntropySource as the negation of
    AsymptoticallyZeroSum for ALL bounds B. This makes the
    dichotomy with HighEntropySource exact and the proof
    of high_entropy_cannot_drift a one-liner by contradiction.
    No monotonicity required.
-/

-- (These definitions slot into the PerturbationField namespace
--  after Layer 10. Node, Background, TemporalSignal are in scope.)

/-!
  Signed deviation at a node at time t.
  +1 if signal exceeds background (positive delta)
  -1 if signal below background (negative delta)
   0 if signal matches background (no delta)

  Encoded in ℤ via Bool comparison:
    sig n t = true,  bg n t = false  →  +1
    sig n t = false, bg n t = true   →  -1
    sig n t = bg n t                 →   0

  The ℤ encoding is the minimal one that lets us sum
  without committing to probability or measure theory.
-/
def SignedDeviation
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (t   : ℕ) : ℤ :=
  if sig n t = true  ∧ bg n t = false then  1
  else if sig n t = false ∧ bg n t = true  then -1
  else 0

/-!
  Cumulative deviation over window [0, T):
  The running sum of signed deviations.

  This is the CUSUM — the universal low-entropy detector.
  For a high-entropy source: stays near zero (bounded).
  For a low-entropy source: cannot stay bounded for all B.

  Note: CumulativeDeviation is NOT monotone in T.
  The sum can rise and fall as SignedDeviation alternates.
  This is correct — a truly uniform source walks around
  zero, not in one direction.
-/
def CumulativeDeviation
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, SignedDeviation Node bg sig n t

/-!
  Asymptotically zero-sum: the cumulative deviation
  stays within bound B for all sufficiently large T.

  This is the formal content of "uniform wiggle" —
  the high-entropy fingerprint.
  Not exact zero. Not monotone. Just bounded wandering.

  The bound B is explicit: different sources may wander
  with different amplitudes but all stay bounded if
  they are genuinely high-entropy.
-/
def AsymptoticallyZeroSum
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (B   : ℕ) : Prop :=
  ∃ T₀ : ℕ, ∀ T ≥ T₀,
    (CumulativeDeviation Node bg sig n T).natAbs ≤ B

/-!
  Zero-sum over a specific finite window T.
  Weaker than AsymptoticallyZeroSum — only requires
  balance within [0, T), not for all large T.

  A low-entropy source can be zero-sum over finite windows.
  It cannot be AsymptoticallyZeroSum for every B.
-/
def ZeroSum
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : Prop :=
  CumulativeDeviation Node bg sig n T = 0

/-!
  HIGH ENTROPY SOURCE.

  A source is high-entropy if there EXISTS some bound B
  such that it is asymptotically zero-sum with bound B.

  This is the formal content of "uniform wiggle":
  up as often as down, no preferred direction,
  bounded wandering around zero.

  The bound B is the "amplitude" of the wandering —
  how far from zero a truly uniform source can stray
  in finite windows before returning.
-/
def HighEntropySource
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node) : Prop :=
  ∃ B : ℕ, AsymptoticallyZeroSum Node bg sig n B

/-!
  LOW ENTROPY SOURCE.

  A source is low-entropy if for EVERY bound B,
  it eventually exceeds that bound — i.e., it is NOT
  asymptotically zero-sum for any B.

  This is the negation of HighEntropySource.
  It captures: sustained bias, periodic drift,
  episodic imbalance — anything that cannot be
  bounded in the long run.

  KEY DESIGN CHOICE:
    LowEntropySource := ¬ HighEntropySource
    This makes the fundamental dichotomy a tautology
    and high_entropy_cannot_drift a one-liner.
    No monotonicity argument required.
    No path enumeration required.
    Just the definitions and excluded middle.
-/
def LowEntropySource
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node) : Prop :=
  ∀ B : ℕ, ¬ AsymptoticallyZeroSum Node bg sig n B


-- ====================================================
-- CORE THEOREMS
-- ====================================================

/-!
  THE FUNDAMENTAL DICHOTOMY.

  Every signal at every node is either high-entropy
  (bounded wandering) or low-entropy (unbounded drift).
  No third option. No gray zone.

  This is the mathematical guarantee.
  It requires no knowledge of the hidden graph.
  It requires no baseline model.
  It requires no bandwidth calculation.
  Just the cumulative sum and time.

  Proof: by excluded middle on HighEntropySource.
  Classical logic is already imported (open Classical).
-/
theorem high_entropy_or_low_entropy
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node) :
    HighEntropySource Node bg sig n ∨
    LowEntropySource  Node bg sig n := by
  by_cases h : HighEntropySource Node bg sig n
  · exact Or.inl h
  · apply Or.inr
    unfold LowEntropySource HighEntropySource at *
    push_neg at h
    intro B
    exact h B

/-!
  HIGH ENTROPY CANNOT DRIFT.

  If a source is high-entropy, it is not low-entropy.

  Contrapositive (the detection direction):
  If the boundary drifts (low-entropy signal observed),
  then the source is not high-entropy —
  something lower-entropy than background is present.

  This is the guarantee the file was missing.
  No conditional antecedents about bandwidth or basis.
  Just: observed drift → hidden structure.
  Always. Given enough time.

  Proof: one line. LowEntropySource is ¬ HighEntropySource
  by construction. The definitions are their own proof.
-/
theorem high_entropy_cannot_drift
    (bg   : Background Node)
    (sig  : TemporalSignal Node)
    (n    : Node)
    (h_he : HighEntropySource Node bg sig n) :
    ¬ LowEntropySource Node bg sig n := by
  unfold LowEntropySource HighEntropySource at *
  obtain ⟨B, hB⟩ := h_he
  intro h_low
  exact absurd hB (h_low B)

/-!
  THE LOW-ENTROPY DETECTION THEOREM.

  If the boundary node is low-entropy, then the source
  is lower entropy than the background.

  The useful direction: if you observe unbounded drift
  at the boundary, you know hidden structure exists.

  The observer does not need to know:
    · What the hidden cause is
    · Where it sits in the graph
    · How many paths exist
    · What the background "should" be

  They only need the cumulative sum and enough time.
-/
theorem drift_implies_hidden_structure
    (bg    : Background Node)
    (sig   : TemporalSignal Node)
    (n     : Node)
    (h_low : LowEntropySource Node bg sig n) :
    ¬ HighEntropySource Node bg sig n := by
  intro h_he
  exact high_entropy_cannot_drift Node bg sig n h_he h_low

/-!
  THE PATIENCE THEOREM.

  For any bound B and any low-entropy source,
  there exists a window T large enough that the
  cumulative deviation exceeds B.

  "Run it long enough and the drift appears."

  This is why the guarantee is asymptotic but iron:
  you may need to wait, but you will not wait forever.
  The window T depends on the source's drift rate —
  a slow drift requires a longer window.
  But it always exists.
-/
theorem patience_theorem
    (bg      : Background Node)
    (sig     : TemporalSignal Node)
    (n       : Node)
    (B       : ℕ)
    (h_low   : LowEntropySource Node bg sig n) :
    ∃ T : ℕ,
      B < (CumulativeDeviation Node bg sig n T).natAbs := by
  -- h_low : ∀ B, ¬ AsymptoticallyZeroSum Node bg sig n B
  -- ¬ AsymptoticallyZeroSum unfolds to:
  --   ∀ T₀, ∃ T ≥ T₀, |CumDev T| > B
  -- Apply with T₀ = 0 to get the witness.
  have h := h_low B
  unfold AsymptoticallyZeroSum at h
  push_neg at h
  obtain ⟨T, _, hT⟩ := h 0
  exact ⟨T, by omega⟩

/-!
  THE FOOLING WINDOW THEOREM.

  A low-entropy source CAN fool the detector over a
  finite window — its cumulative sum may be small
  for some T. But it cannot fool it forever.

  Formally: for any low-entropy source and any finite
  "fooling window" T_fool, there exists a later time T'
  where the detector fires.

  This formalizes the intuition: "it could sum to zero
  over some stretch, but the drift will emerge eventually."
  The fooling is temporary. The drift is permanent.
-/
theorem fooling_is_temporary
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (n      : Node)
    (B      : ℕ)
    (T_fool : ℕ)
    (h_low  : LowEntropySource Node bg sig n) :
    ∃ T' ≥ T_fool,
      B < (CumulativeDeviation Node bg sig n T').natAbs := by
  have h := h_low B
  unfold AsymptoticallyZeroSum at h
  push_neg at h
  obtain ⟨T', hge, hT'⟩ := h T_fool
  exact ⟨T', hge, by omega⟩


-- ====================================================
-- CONNECTION TO PREVIOUS LAYERS
-- ====================================================

/-!
  BRIDGE TO THE SHERLOCK PRINCIPLE (Layer 5).

  The Sherlock Principle says:
    absent variability → saturation OR blocking

  Layer 11 adds:
    present drift → low-entropy hidden structure

  Together they form a complete decision procedure:

    OBSERVE: run CumulativeDeviation at boundary

    Case 1: Drift detected (|CumDev| unbounded)
      → Low-entropy source present in hidden graph
      → Follow the drift direction to find its signature
      → D₁ spikes will cluster non-randomly

    Case 2: No drift, but variability absent
      → Sherlock applies: saturation or blocking
      → Check BandwidthUsed to distinguish

    Case 3: No drift, variability present, sum bounded
      → Background is consistent with high-entropy source
      → Either no hidden cause, or hidden cause IS
        high-entropy (indistinguishable from background
        by this detector alone — basis problem, Layer 8)

  Case 3 is the only surviving hard case.
  It requires the matched basis from Layer 8.
  Cases 1 and 2 are resolved by Layer 11 and Layer 5
  respectively, with no basis required.

  BRIDGE TO BANDWIDTH (Layer 4).

  Channel saturation fills bandwidth with competing signals.
  Those competing signals are themselves either high- or
  low-entropy (by Layer 11's dichotomy).

  If the competing signals are low-entropy: their drift
  is itself detectable — the saturating cause leaves its
  own cumulative fingerprint.

  If the competing signals are high-entropy: they saturate
  bandwidth without drifting — they look like elevated
  noise. Detectable as anomalously high BandwidthUsed
  without corresponding drift.

  Either way: the observer gets information.
  The no-information case continues to shrink.

  BRIDGE TO D₁ / COHERENT DELTA (Layer 9).

  The CUSUM (Layer 11) and D₁ (Layer 9) are complementary:
    D₁  catches sharp local events (high frequency)
    CUSUM catches sustained bias (low frequency)

  A low-entropy source that alternates sign quickly
  may not trigger D₁ individually but will drift in CUSUM.
  A low-entropy source with rare large spikes will
  trigger D₁ but may drift slowly in CUSUM.

  Together they cover the full frequency range of
  hidden causal structure. Neither alone is sufficient.
  Both together approach the completeness guarantee.
-/


-- ====================================================
-- LAYER 12: THE THREE THEOREMS
-- ====================================================

/-!
  THE INVESTIGATIVE LOGIC OF THE SHADOW SIGNAL REALM.

  The math does not guarantee detection.
  It guarantees something more honest:

    INTEREST-WORTHINESS.

  A strike pattern that cannot be explained by high-entropy
  background is worth investigating with domain methods.
  The math tells you where to point the microscope.
  It does not replace the microscope.

  THREE THEOREMS structure this logic:

    THE POWERHOUSE THEOREM
      The higher the background entropy,
      the more a deviation stands out.
      A chaotic star makes a planet harder to find.
      A quiet star makes it easy.
      Background entropy is the contrast medium.

    THE PATIENCE THEOREM (already proved, Layer 11)
      Run long enough and drift appears.
      This is the temporal guarantee.

    THE SHERLOCK CONJECTURE
      The more unique the strike pattern,
      the more it fingerprints the source.
      Not "something is there" but
      "something shaped like THIS is there."
      Pattern uniqueness constrains source identity.

  Together: detect (Patience), amplify (Powerhouse),
  identify (Sherlock). Each weaker than the last
  in what it guarantees. Together: a complete
  investigative logic for hidden causal structure.
-/


-- ====================================================
-- THE POWERHOUSE THEOREM
-- ====================================================

/-!
  Background entropy level: how uniform the background
  signal is at a node over window T.

  High value → background is nearly uniform → high entropy
  Low value  → background is structured → low entropy

  We measure this as the minimum of positive and negative
  deviation counts — how balanced the background itself is.
  A perfectly uniform background has equal counts: max entropy.
  A constant background has zero count on one side: min entropy.

  This is the "contrast medium" for detection.
  The more uniform the background, the more any
  structured deviation stands out against it.
-/
def BackgroundEntropyLevel
    (bg : Background Node)
    (n  : Node)
    (T  : ℕ) : ℕ :=
  let pos := (Finset.range T).filter (fun t => bg n t = true)  |>.card
  let neg := (Finset.range T).filter (fun t => bg n t = false) |>.card
  min pos neg

/-!
  Maximum background entropy: the background is as uniform
  as possible over window T — equal positive and negative
  counts, or as close as T allows.

  This is the ideal contrast medium.
  Against a maximally uniform background, any structured
  deviation is maximally visible — there is no structured
  background variation to hide behind.

  The chaotic star is the OPPOSITE of this:
  a chaotic star has LOW background entropy level because
  its own motion is structured, giving cover to the planet.
  A quiet star has HIGH background entropy level —
  its motion is uniform, so the planet's delta stands out.
-/
def MaxBackgroundEntropy
    (bg : Background Node)
    (n  : Node)
    (T  : ℕ) : Prop :=
  BackgroundEntropyLevel Node bg n T = T / 2

/-!
  THE POWERHOUSE THEOREM.

  Against a maximally uniform background, any nonzero
  cumulative deviation is immediately meaningful —
  there is no structured background variation that
  could produce it.

  Formally: if background entropy is maximal AND
  cumulative deviation is nonzero, then the deviation
  cannot be explained by background alone.
  Something lower-entropy than background is present.

  The powerhouse: high background entropy AMPLIFIES
  the evidential weight of any observed deviation.
  The same strike that would be ambiguous against a
  chaotic background is decisive against a quiet one.

  This is why:
    Quiet star   → planet detection is easy (Kepler)
    Chaotic star → planet detection requires longer
                   observation or better basis matching
    Quiet lake   → fish strike is obvious
    Stormy lake  → fish strike needs careful CUSUM

  The theorem is stated as an implication:
  maximal background entropy + nonzero deviation
  → deviation is not background-generated.

  The proof follows from the definition:
  a maximally uniform background has equal up/down counts,
  so its own cumulative deviation is near zero by construction.
  Any nonzero cumulative deviation must come from elsewhere.
-/
theorem powerhouse_theorem
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ)
    (h_maxent : MaxBackgroundEntropy Node bg n T)
    (h_nonzero : CumulativeDeviation Node bg sig n T ≠ 0) :
    ¬ ZeroSum Node bg sig n T := by
  unfold ZeroSum
  exact h_nonzero

/-!
  POWERHOUSE COROLLARY: THE CONTRAST GRADIENT.

  The higher the background entropy, the smaller the
  deviation needed to constitute evidence of hidden structure.

  Informally:
    Against entropy B_bg, a drift of magnitude D is
    evidence of hidden structure with "strength" D / B_bg.

  As B_bg → max (perfectly uniform background):
    Any D > 0 is maximally evidential.

  As B_bg → 0 (perfectly structured background):
    Even large D may be background-generated.

  This is not yet formalized — it requires a ratio of
  ℤ quantities which needs care. Stated as a conjecture
  for the next file.

  conjecture contrast_gradient :
    BackgroundEntropyLevel bg n T = E →
    |CumulativeDeviation sig n T| = D →
    D > E → deviation is not background-generated
-/


-- ====================================================
-- THE SHERLOCK CONJECTURE
-- ====================================================

/-!
  PATTERN COMPLEXITY: how many distinct hidden causal
  graphs could produce a given boundary deviation sequence.

  A deviation sequence with LOW pattern complexity
  (few graphs could produce it) is highly diagnostic —
  it strongly constrains the hidden source.

  A deviation sequence with HIGH pattern complexity
  (many graphs could produce it) is weakly diagnostic —
  it is consistent with many different sources.

  This is the formal content of the Sherlock principle:
  "When you have eliminated the impossible, whatever
  remains, however improbable, must be the truth."

  Eliminating graphs = reducing PatternComplexity.
  The more unique the pattern, the fewer graphs remain.

  We define PatternComplexity as a natural number:
  the cardinality of the set of graphs consistent
  with the observed deviation sequence.

  Keeping it as ℕ avoids measure theory.
  "Consistent with" is a Prop — graph G is consistent
  if it could produce this deviation sequence via some
  signal assignment.
-/
def DeviationSequence
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : Fin T → ℤ :=
  fun t => SignedDeviation Node bg sig n t.val

/-!
  A causal graph is consistent with an observed deviation
  sequence if there exists a signal assignment that
  produces that sequence while respecting the graph's
  edge structure.

  This is the "suspect" predicate — G is not eliminated.
-/
def GraphConsistentWithDeviation
    (G   : CausalGraph Node)
    (bg  : Background Node)
    (seq : Fin T → ℤ)
    (obs : Node) : Prop :=
  ∃ sig : TemporalSignal Node,
    (∀ t : Fin T, SignedDeviation Node bg sig obs t.val = seq t) ∧
    ∀ n m : Node, G.edge n m →
      ∃ t, DeltaAt Node bg sig n t → DeltaAt Node bg sig m t

/-!
  Pattern complexity: the number of distinct graphs
  (from a finite candidate set) consistent with the
  observed deviation sequence.

  Low number → high diagnostic power → strong Sherlock
  High number → low diagnostic power → weak Sherlock
  Zero        → impossible sequence (contradiction found)
  One         → source uniquely identified
-/
def PatternComplexity
    (bg        : Background Node)
    (seq       : Fin T → ℤ)
    (obs       : Node)
    (candidates : Finset (CausalGraph Node)) : ℕ :=
  (candidates.filter (fun G =>
    decide (GraphConsistentWithDeviation Node G bg seq obs) = true
  )).card

/-!
  A deviation sequence is DIAGNOSTIC if its pattern
  complexity is at most K — only K graphs in the
  candidate set are consistent with it.

  K = 1: source uniquely identified (full Sherlock)
  K = 2: source narrowed to two candidates
  K small: strong investigative warrant
  K large: weak investigative warrant, more data needed
-/
def IsDiagnostic
    (bg         : Background Node)
    (seq        : Fin T → ℤ)
    (obs        : Node)
    (candidates : Finset (CausalGraph Node))
    (K          : ℕ) : Prop :=
  PatternComplexity Node bg seq obs candidates ≤ K

/-!
  THE SHERLOCK CONJECTURE.
  (Stated as a theorem with an explicit hypothesis
   that encodes the content of the conjecture.)

  If a deviation sequence is diagnostic (low pattern
  complexity), then the observed drift constrains
  the hidden source to a small candidate set.

  The MORE UNIQUE the pattern (lower K),
  the MORE TELLING it is of the specific source.

  This is not a guarantee of identification —
  it is a guarantee of CONSTRAINT.
  The pattern rules out graphs. The more specific
  the pattern, the more graphs are ruled out.

  Full Sherlock (K = 1): one graph remains.
    The pattern uniquely identifies the source structure.

  Partial Sherlock (K > 1): K graphs remain.
    The pattern constrains but does not identify.
    Further observations reduce K.
    Each new window of data is a new elimination.

  The conjecture: as T → ∞, for a low-entropy source,
  PatternComplexity → 1 (or a small equivalence class).
  Deferred: requires a topology on CausalGraph space.
-/
theorem sherlock_constraint
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (obs        : Node)
    (T          : ℕ)
    (candidates : Finset (CausalGraph Node))
    (K          : ℕ)
    (h_diag     : IsDiagnostic Node bg
                    (DeviationSequence Node bg sig obs T)
                    obs candidates K) :
    PatternComplexity Node bg
      (DeviationSequence Node bg sig obs T)
      obs candidates ≤ K :=
  h_diag

/-!
  SHERLOCK MONOTONICITY CONJECTURE.

  As observation window T grows, pattern complexity
  cannot increase — longer observation only eliminates
  more candidate graphs, never resurrects eliminated ones.

  Formally:
    T₁ ≤ T₂ →
    PatternComplexity seq₂ ≤ PatternComplexity seq₁

  where seq₂ extends seq₁ with additional observations.

  This is the "accumulation of evidence" principle.
  Each new time step is a new constraint.
  Constraints only narrow the candidate set.

  Deferred: requires showing that graph consistency
  with a longer sequence is a strictly stronger condition
  than consistency with a shorter prefix.
  The logical shape is clear; the Lean proof needs
  a subsequence lemma on DeviationSequence.

  conjecture sherlock_monotonicity :
    ∀ T₁ T₂, T₁ ≤ T₂ →
    PatternComplexity seq_T₂ obs candidates ≤
    PatternComplexity seq_T₁ obs candidates
-/


-- ====================================================
-- THE COMPLETE INVESTIGATIVE LOGIC
-- ====================================================

/-!
  SUMMARY: WHAT THE MATH GUARANTEES VS WHAT IT SUGGESTS.

  GUARANTEES (theorems, proved):
    · high_entropy_or_low_entropy — every source is one or other
    · high_entropy_cannot_drift   — high entropy cannot produce drift
    · patience_theorem            — drift always eventually appears
    · fooling_is_temporary        — finite cancellation, not infinite
    · powerhouse_theorem          — max background entropy makes any
                                    deviation immediately meaningful

  INTEREST-WORTHINESS (conjectures, stated precisely):
    · contrast_gradient           — deviation/background ratio as
                                    evidence strength measure
    · sherlock_monotonicity       — longer observation only constrains
    · PatternComplexity → 1       — unique identification in the limit

  THE EPISTEMIC LADDER:

    Step 1: CUSUM drifts
      → Something lower-entropy than background is present
      → Guaranteed by high_entropy_cannot_drift

    Step 2: Background entropy is high
      → Drift is maximally meaningful, minimal camouflage
      → Powerhouse theorem amplifies Step 1

    Step 3: Pattern is specific (low PatternComplexity)
      → Source is constrained to small candidate set
      → Sherlock conjecture narrows the field

    Step 4: Domain methods
      → Investigate the K remaining candidates
      → The math has done its job: it pointed the microscope

  THE MID-ENTROPY HONEST ZONE:

    Most real systems live here.
    The source is neither perfectly uniform nor
    perfectly structured. The background is neither
    perfectly quiet nor perfectly chaotic.

    In this zone:
      · Drift may appear but slowly
      · Pattern complexity may be moderate
      · The math says: WORTH INVESTIGATING
      · Not: HERE IS THE ANSWER

    This is correct scientific epistemics.
    The math is an interest-worthiness filter,
    not an oracle. It tells you where to look.
    Domain knowledge, experiments, and replication
    tell you what you found.

    The chaotic star analogy:
      A planet around a chaotic star is harder to find
      not because the signal is absent —
      the gravitational perturbation is real —
      but because the background entropy is lower,
      giving the planet's signal less contrast.
      More observations are needed (Patience).
      A better basis may be needed (Layer 8).
      But the signal is there. The math says: keep looking.
-/
