import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

namespace PerturbationField

/-!
  PERTURBATION FIELD — SIGNAL VARIABILITY THROUGH HIDDEN CAUSAL GRAPHS
  ─────────────────────────────────────────────────────────────────────
  Core intuition:

  Information propagates not only through direct state transfer,
  but through perturbations imposed onto an already active
  dynamical background.

  THREE LAYERS:
    Primary field   — the normal background causal activity
    Delta           — deviation from that background at a node
    Perturbation    — how that delta propagates through the graph

  The observer never sees the hidden cause directly.
  They see the delta pattern at the observable boundary.

  EXAMPLES:
    Stellar wobble       → planet's delta on star motion
    Bobber micro-motion  → fish's delta on wave background
    Cancer incidence     → virus flux delta on population baseline
    Galactic rotation    → dark matter delta on visible mass dynamics

  KEY CLAIM (the Bandwidth Principle):
    A delta riding on the perturbation field has LOW BANDWIDTH
    compared to the primary signals in the graph.

    For the delta to fail to reach the observable boundary,
    the delta channel's capacity budget must be exhausted —
    other causal activity fills the available bandwidth,
    crowding out the variability signal.

    This replaces the earlier "perfect inverse" framing.
    A perfect inverse requires precise anti-coordination.
    Bandwidth exhaustion requires only that the channel
    is full — a far more natural and physically honest
    failure mode.

    TWO DISTINCT FAILURE MODES at the boundary:
      SATURATION  — channel loud, expected variability absent
                    something else filled the bandwidth
                    fingerprint: high activity, wrong pattern

      BLOCKING    — channel quiet, expected variability absent
                    low-entropy structure actively routing away
                    fingerprint: anomalous silence at boundary

    Both are detectable. Neither is invisible.

  DESIGN NOTES:
    1. Signal is kept abstract (Bool over time) — not committed
       to numeric, continuous, or probabilistic interpretation.
       Probability is not primitive here; it is downstream of
       graph geometry.

    2. Delta is purely propositional: ∃ t, s(n,t) ≠ background(n,t)
       No sums, no squares, no division. Avoids real-valued
       machinery that caused proof friction in earlier files.

    3. Combinatorial explosion is avoided by the same strategy
       as the radar and basin files: we never enumerate paths.
       We reason about path existence and capacity budget,
       not path content.

    4. The capacity budget is the interesting object.
       It is defined as a natural number bound on distinct
       delta events observable per time window — keeping
       everything in ℕ and avoiding measure theory.

    5. The bandwidth/capacity framing connects naturally to
       the basin entropy bound in InterfaceConfig.lean:
         basin_local_complexity ≤ basin_entropy
       is already a bandwidth statement in disguise.
       The delta channel can carry at most basin_entropy
       distinct signal configurations.
-/


-- ====================================================
-- LAYER 1: CORE SIGNAL PRIMITIVES
-- ====================================================

variable (Node : Type) [DecidableEq Node] [Fintype Node]

/-!
  A temporal signal: every node carries a Boolean state
  at every time step.

  Boolean is deliberate. Signal means "a distinction that
  varies over time" — not a magnitude, not a probability.
  Up/down. Present/absent. Affected/unaffected.
  The same structure works for on/off virus presence,
  above/below incidence threshold, wobble direction.
-/
abbrev TemporalSignal := Node → ℕ → Bool

/-!
  Background field: the expected "normal" state of each
  node at each time. This is what the signal would look
  like if no hidden perturbation existed.

  In the bobber example: the normal wave pattern.
  In the stellar wobble: the expected star trajectory.
  In epidemiology: the baseline incidence rate.
-/
abbrev Background := Node → ℕ → Bool

/-!
  A delta event: node n deviates from background at time t.
  This is the atomic unit of perturbation information.
  One unit of bandwidth consumed.
-/
def DeltaAt
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (t   : ℕ) : Prop :=
  sig n t ≠ bg n t

/-!
  A node produces a delta: it deviates from background
  at some point in time.

  This is the "fish tugging the bobber" condition —
  not necessarily a big effect, just a detectable
  departure from the expected pattern.
-/
def ProducesDelta
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node) : Prop :=
  ∃ t, DeltaAt Node bg sig n t

/-!
  A node has variability: its state is not constant over
  the time window [0, T).

  This is separate from ProducesDelta — variability is
  about the signal itself changing, delta is about
  deviation from background. A node can have variability
  without a background reference.
-/
def HasVariability
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : Prop :=
  ∃ t₁ t₂, t₁ < T ∧ t₂ < T ∧ sig n t₁ ≠ sig n t₂

/-!
  A node is a variability source: it produces deltas AND
  has internal variability — its departures from background
  are themselves non-constant.

  This is the key source condition. A virus population
  that merely exists is not enough. It must *fluctuate*.
  The fluctuation is what creates the propagating delta.
-/
def VariabilitySource
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : Prop :=
  ProducesDelta Node bg sig n ∧ HasVariability Node sig n T


-- ====================================================
-- LAYER 2: GRAPH STRUCTURE AND PATHS
-- ====================================================

/-!
  A causal graph: directed edges between nodes.
  Hidden structure lives here.
-/
structure CausalGraph where
  edge : Node → Node → Prop

/-!
  A causal path from source to target:
  a finite sequence of nodes where each consecutive
  pair is connected by an edge.

  We keep paths abstract — we reason about their
  existence and count, not their content.
  This is what avoids combinatorial explosion.
-/
structure CausalPath
    (G      : CausalGraph Node)
    (source : Node)
    (target : Node) where
  nodes    : List Node
  nonempty : nodes ≠ []
  valid    : ∀ i, i + 1 < nodes.length →
    G.edge (nodes.get ⟨i, by omega⟩)
           (nodes.get ⟨i + 1, by omega⟩)

/-!
  Path existence: there is at least one causal path
  from source to target through the graph.

  This is the only path property the main theorem needs.
  We never enumerate which paths exist.
-/
def PathExists
    (G      : CausalGraph Node)
    (source : Node)
    (target : Node) : Prop :=
  Nonempty (CausalPath Node G source target)

/-!
  A node lies on a path: it appears in the path's
  node sequence.
-/
def NodeOnPath
    {G      : CausalGraph Node}
    {source : Node}
    {target : Node}
    (p      : CausalPath Node G source target)
    (n      : Node) : Prop :=
  n ∈ p.nodes


-- ====================================================
-- LAYER 3: THE DELTA AND HOW IT PROPAGATES
-- ====================================================

/-!
  Delta propagation axiom:
  If a source node produces a delta, and there is a
  causal path to a target, and sufficient bandwidth
  exists in the channel, then the target inherits
  the delta.

  Bandwidth is now an explicit parameter — the delta
  only propagates if the channel has room for it.
  This is the key change from the earlier formulation.

  The exact propagation mechanism is domain-dependent:
    Kepler case:       gravity propagates the wobble
    Epidemiology case: infection chains propagate the shift
    Bobber case:       water tension propagates the tug
  The mathematics is the same regardless of domain.
-/
def PropagatesDelta
    (G        : CausalGraph Node)
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (source   : Node)
    (target   : Node)
    (bw_avail : ℕ) : Prop :=
  bw_avail > 0 →
  ProducesDelta Node bg sig source →
  PathExists Node G source target →
  ProducesDelta Node bg sig target

/-!
  The perturbation field: for each node, whether it
  participates in delta propagation from a source.

  This is the "shadow field" — the structured medium
  that carries the perturbation. Not the primary signal.
  Not noise. The organized residue of the delta
  moving through the graph.
-/
def PerturbationField
    (G      : CausalGraph Node)
    (source : Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node) :
    Finset Node :=
  Finset.univ.filter (fun n =>
    PathExists Node G source n ∧
    ProducesDelta Node bg sig n)


-- ====================================================
-- LAYER 4: THE CAPACITY BUDGET
-- ====================================================

/-!
  CHANNEL CAPACITY — the bandwidth budget.

  The delta channel between source and observable has
  finite capacity: a maximum number of distinct delta
  events it can carry per time window T.

  This is the key new primitive replacing cancellation.

  Physical interpretation:
    The channel capacity is determined by the number of
    distinguishable states the intermediate nodes can
    carry simultaneously. Intermediate causal activity
    consumes this budget. When the budget is exhausted,
    new delta events — including variability signals —
    cannot propagate through.

  Connection to existing files:
    basin_local_complexity ≤ basin_entropy
    is the same statement: the channel carries at most
    basin_entropy distinct configurations.
    Channel capacity IS basin entropy, geometrically.
-/
def ChannelCapacity
    (T : ℕ)
    (path_count : ℕ) : ℕ :=
  T * path_count
  -- Simplified: capacity scales with window size
  -- and number of independent paths.
  -- A richer definition would factor in node state space.
  -- This is the seed version.

/-!
  Bandwidth used by competing causal signals at node n
  in window T: the count of delta events at n that are
  NOT from the variability source of interest.

  These are the signals competing for channel capacity —
  the "noise" in the bandwidth sense.
  Not random noise. Structured causal signals from
  OTHER hidden causes, filling the same channel.
-/
def BandwidthUsed
    (bg  : Background Node)
    (sig : TemporalSignal Node)
    (n   : Node)
    (T   : ℕ) : ℕ :=
  (Finset.range T).filter
    (fun t => decide (DeltaAt Node bg sig n t) = true) |>.card

/-!
  Bandwidth available for the variability signal:
  total capacity minus what competing signals consume.

  If this is zero, the variability delta cannot propagate
  through this node — bandwidth exhaustion.

  This is the capacity budget check.
-/
def BandwidthAvailable
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (n          : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ) : ℕ :=
  let capacity := ChannelCapacity T path_count
  let used     := BandwidthUsed Node bg sig n T
  if used + bw_signal ≤ capacity
  then capacity - used
  else 0

/-!
  Bandwidth sufficient: the variability signal fits
  within the remaining channel capacity.

  When this holds: delta propagates to boundary.
  When this fails: delta is crowded out — bandwidth
  exhaustion, NOT cancellation.
-/
def BandwidthSufficient
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (n          : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ) : Prop :=
  BandwidthAvailable Node bg sig n T path_count bw_signal > 0

/-!
  The two distinct failure modes — now formally separated.

  SATURATION: channel is loud but variability absent.
  Something else filled the budget.
  Fingerprint: high BandwidthUsed, low BandwidthAvailable.

  BLOCKING: channel is quiet but variability absent.
  Low-entropy structure routing signals away.
  Fingerprint: low BandwidthUsed AND low BandwidthAvailable
               — which means capacity itself is small,
               i.e. path_count is small,
               i.e. a bottleneck exists.
-/
def ChannelSaturated
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (n          : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ) : Prop :=
  BandwidthUsed Node bg sig n T ≥
    ChannelCapacity T path_count

def ChannelBlocked
    (T          : ℕ)
    (path_count : ℕ) : Prop :=
  ChannelCapacity T path_count = 0

/-!
  Key lemma: saturation and blocking are mutually
  distinguishable from the boundary.

  Saturation  → BandwidthUsed is high (noisy channel)
  Blocking    → BandwidthUsed is low AND path_count = 0
                (silent channel, bottleneck present)

  These have different fingerprints at the observable.
  Neither is "invisible absence of variability."
-/
lemma saturation_ne_blocking
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (n          : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ)
    (h_sat  : ChannelSaturated Node bg sig n T path_count bw_signal)
    (h_used : BandwidthUsed Node bg sig n T > 0) :
    ¬ ChannelBlocked T path_count := by
  unfold ChannelBlocked ChannelCapacity
  intro h_zero
  simp [h_zero] at h_sat
  exact Nat.not_eq_zero_of_lt h_used
    (Nat.eq_zero_of_le_zero h_sat)


-- ====================================================
-- LAYER 5: MAIN THEOREMS
-- ====================================================

/-!
  DELTA PROPAGATION THEOREM (bandwidth version).

  If:
    · source produces a delta
    · a causal path exists from source to obs
    · the graph propagates deltas along paths
    · bandwidth is sufficient (channel not exhausted)

  Then: obs produces a delta.

  The hidden structure is never enumerated.
  The proof is purely structural.
  Bandwidth replaces the cancellation condition.
-/
theorem delta_reaches_observable
    (G          : CausalGraph Node)
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (source     : Node)
    (obs        : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ)
    (h_src      : ProducesDelta Node bg sig source)
    (h_path     : PathExists Node G source obs)
    (h_prop     : PropagatesDelta Node G bg sig source obs bw_signal)
    (h_bw       : BandwidthSufficient Node bg sig obs T
                    path_count bw_signal) :
    ProducesDelta Node bg sig obs :=
  h_prop (Nat.pos_of_ne_zero (by
    unfold BandwidthSufficient BandwidthAvailable at h_bw
    split_ifs at h_bw with hif
    · exact Nat.not_eq_zero_of_lt h_bw ∘ Nat.eq_zero_of_le_zero ∘
        Nat.le_of_lt_succ ∘ Nat.lt_succ_of_le ∘ Nat.le_refl
    · simp at h_bw)) h_src h_path

/-!
  PERTURBATION FIELD MEMBERSHIP (bandwidth version).

  If bandwidth is sufficient and delta propagates,
  obs is in the perturbation field of source.
-/
theorem obs_in_perturbation_field
    (G          : CausalGraph Node)
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (source     : Node)
    (obs        : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ)
    (h_src      : ProducesDelta Node bg sig source)
    (h_path     : PathExists Node G source obs)
    (h_prop     : PropagatesDelta Node G bg sig source obs bw_signal)
    (h_bw       : BandwidthSufficient Node bg sig obs T
                    path_count bw_signal) :
    obs ∈ PerturbationField Node G source bg sig := by
  unfold PerturbationField
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h_path, h_prop
    (by unfold BandwidthSufficient BandwidthAvailable at h_bw
        split_ifs at h_bw with hif
        · exact Nat.pos_of_ne_zero (Nat.ne_of_gt
            (Nat.lt_of_lt_of_le h_bw (Nat.le_refl _)))
        · exact absurd h_bw (Nat.not_lt.mpr (Nat.le_refl _)))
    h_src h_path⟩

/-!
  THE SHERLOCK PRINCIPLE (bandwidth version).

  If expected variability is ABSENT at the boundary,
  then one of two detectable conditions must hold:

    (A) SATURATION: the channel was full —
        other causal signals consumed the budget.
        The channel is loud. Something else is in there.

    (B) BLOCKING: the channel capacity is zero —
        path_count = 0, a bottleneck routes signals away.
        The channel is silent. A low-entropy structure exists.

  In either case: the absence of variability is itself
  evidence about hidden graph structure.
  There is no "invisible" failure mode.

  Compare to the old framing: absence implied a perfect
  inverse — requiring precise coordination.
  Now: absence implies saturation OR blocking —
  both physically natural, both detectable.
-/
theorem absent_variability_implies_saturation_or_blocking
    (G          : CausalGraph Node)
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (source     : Node)
    (obs        : Node)
    (T          : ℕ)
    (path_count : ℕ)
    (bw_signal  : ℕ)
    (h_src      : ProducesDelta Node bg sig source)
    (h_path     : PathExists Node G source obs)
    (h_prop     : PropagatesDelta Node G bg sig source obs bw_signal)
    (h_absent   : ¬ ProducesDelta Node bg sig obs) :
    ChannelSaturated Node bg sig obs T path_count bw_signal ∨
    ChannelBlocked T path_count := by
  by_contra h
  push_neg at h
  obtain ⟨h_not_sat, h_not_blocked⟩ := h
  apply h_absent
  apply h_prop
  · unfold BandwidthSufficient BandwidthAvailable
    unfold ChannelSaturated at h_not_sat
    unfold ChannelBlocked ChannelCapacity at h_not_blocked
    simp only [ChannelCapacity]
    have hpos : ChannelCapacity T path_count > 0 :=
      Nat.pos_of_ne_zero h_not_blocked
    have hroom : BandwidthUsed Node bg sig obs T + bw_signal ≤
                 ChannelCapacity T path_count :=
      Nat.le_of_not_lt h_not_sat
    simp [show BandwidthUsed Node bg sig obs T + bw_signal ≤
              ChannelCapacity T path_count from hroom]
    omega
  · exact h_src
  · exact h_path

/-!
  VARIABILITY PROPAGATION THEOREM (bandwidth version).

  Source variability reaches the boundary
  when bandwidth is sufficient.

  The virus-cancer connection:
  flux in the upstream cause → detectable flux downstream,
  as long as the channel between them has room
  for the variability signal.
-/
def PropagatesVariability
    (G          : CausalGraph Node)
    (bg         : Background Node)
    (sig        : TemporalSignal Node)
    (source     : Node)
    (obs        : Node)
    (T          : ℕ)
    (bw_signal  : ℕ) : Prop :=
  VariabilitySource Node bg sig source T →
  PathExists Node G source obs →
  bw_signal > 0 →
  HasVariability Node sig obs T

theorem variability_reaches_boundary
    (G           : CausalGraph Node)
    (bg          : Background Node)
    (sig         : TemporalSignal Node)
    (source      : Node)
    (obs         : Node)
    (T           : ℕ)
    (path_count  : ℕ)
    (bw_signal   : ℕ)
    (h_vsrc      : VariabilitySource Node bg sig source T)
    (h_path      : PathExists Node G source obs)
    (h_var_prop  : PropagatesVariability Node G bg sig source obs T
                     bw_signal)
    (h_bw        : BandwidthSufficient Node bg sig obs T
                     path_count bw_signal) :
    HasVariability Node sig obs T := by
  apply h_var_prop h_vsrc h_path
  unfold BandwidthSufficient BandwidthAvailable at h_bw
  split_ifs at h_bw with hif
  · exact Nat.pos_of_ne_zero (by omega)
  · exact absurd h_bw (by simp)


-- ====================================================
-- LAYER 6: ENTROPY AND BANDWIDTH CAPACITY
-- ====================================================

/-!
  PATH CONCENTRATION.

  How many paths from source to obs pass through node v.
  High concentration at a single node = low entropy graph.
  That node is a bottleneck — it alone controls capacity.

  Connection to bandwidth:
  A bottleneck node limits path_count through it,
  which limits ChannelCapacity through that segment,
  which shrinks BandwidthAvailable for the delta signal.

  "AAAAA" graph: all paths through A.
    A's local bandwidth IS the channel bandwidth.
    A filling up = channel saturated, delta crowded out.
    A having zero paths = channel blocked entirely.

  "BDFBAC" graph: paths distributed across many nodes.
    No single node controls the budget.
    Much harder to saturate or block.
    Delta finds bandwidth on alternative paths.
-/
def PathConcentration
    (G      : CausalGraph Node)
    (source : Node)
    (obs    : Node)
    (v      : Node)
    (paths  : Finset (CausalPath Node G source obs)) : ℕ :=
  (paths.filter (fun p => decide (NodeOnPath p v) = true)).card

/-!
  GRAPH PATH ENTROPY (simplified).

  A graph has high path entropy between source and obs
  if no single node dominates the path structure.
  Every node appears on at most ε paths.

  High entropy → bandwidth distributed across many nodes
               → hard to saturate the full channel
               → delta finds a route through

  Low entropy  → bandwidth concentrated at few nodes
               → easy to saturate or block at those nodes
               → delta may be crowded out locally
-/
def HighPathEntropy
    (G      : CausalGraph Node)
    (source : Node)
    (obs    : Node)
    (ε      : ℕ)
    (paths  : Finset (CausalPath Node G source obs)) : Prop :=
  ∀ v : Node,
    PathConcentration Node G source obs v paths ≤ ε

/-!
  BANDWIDTH DISTRIBUTION LEMMA.

  In a high-entropy graph, total channel capacity is
  distributed across many nodes — no single node
  controls more than ε/total fraction of paths.

  Therefore: to saturate the FULL channel, competing
  signals must fill bandwidth at EVERY high-concentration
  node simultaneously.

  The coordination cost of doing this grows with
  graph entropy — exactly as the coordination cost
  of the old "inverse" grew with entropy.

  But now the mechanism is cleaner:
  it is not about producing anti-patterns,
  it is about filling a budget at enough nodes
  to crowd out the variability signal on all paths.

  CONJECTURE (exploratory):
    HighPathEntropy G source obs ε paths ∧
    paths.card > ε →
    full channel saturation requires competing signals
    at ≥ paths.card / ε distinct nodes simultaneously.

  Deferred: requires Fintype on paths.
  The logical shape is clear.
-/

/-!
  THE CAPACITY BUDGET CONJECTURE.

  Sufficient path entropy makes full channel saturation
  geometrically costly — not impossible, but requiring
  coordinated competing signals across many nodes.

  That coordination is itself a low-entropy structure,
  detectable by the radar file's asymmetry theorems.

  So: high entropy graph → either delta propagates,
      OR saturation requires detectable coordination,
      OR blocking requires detectable bottleneck.

  The observer always gets information.
  The specific flavor of information tells them
  which failure mode occurred.

  conjecture entropy_makes_saturation_costly :
    HighPathEntropy G source obs ε paths →
    paths.card > ε * Fintype.card Node →
    full_saturation_requires_coordination G source obs

  Deferred to future file with path Fintype infrastructure.
-/


-- ====================================================
-- LAYER 7: CONNECTION TO PREVIOUS FILES
-- ====================================================

/-!
  BRIDGE TO CAUSAL RADAR (CausalGraph.lean).

  Channel saturation — if it exists — appears as
  elevated structural_diversity in the radar file.

  Because: competing signals filling the channel must
  themselves pass through boundary nodes, creating
  asymmetric_interface readings that the radar detects
  as positive accumulated_asymmetry.

  Channel blocking appears as anomalously LOW
  structural_diversity — the bottleneck suppresses
  asymmetry by routing everything through one node,
  which itself stands out as a singular high-asymmetry
  point.

  Consequence:
    Delta reaches boundary (bandwidth sufficient)   → observable
    Channel saturated (competing signals present)   → radar loud
    Channel blocked (bottleneck present)            → radar silent + bottleneck bright

  All three cases give the observer information.
  There is no truly dark outcome.

  BRIDGE TO INTERFACE CONFIG (InterfaceConfig.lean).

  The capacity budget IS the basin entropy bound:
    basin_local_complexity ≤ basin_entropy ≤ |Signal|

  Channel capacity = how many distinct signal
  configurations the basin can carry.
  BandwidthUsed = how many configurations are already
  occupied by competing signals.
  BandwidthAvailable = remaining basin entropy budget
  for the variability delta.

  The three-level sandwich theorem already proves
  that observable complexity is bounded by signal entropy.
  The bandwidth framing makes explicit WHY:
  the channel cannot carry more than its entropy allows.

  BRIDGE TO GATEWAY (first file).

  A channel blocked by a bottleneck corresponds to
  a gateway_region with small card — the forced overlap
  theorem then shows multiple outcomes route through
  the same gateway node, making it detectable via
  the pigeonhole argument.

  Saturation at a bottleneck node corresponds to
  that node handling more distinct signals than its
  local bandwidth allows — again detectable.
-/


-- ====================================================
-- LAYER 8: THE OBSERVER BASIS PROBLEM
-- ====================================================

/-!
  THE BOBBER PROBLEM.

  A delta can propagate with sufficient bandwidth,
  arrive at the boundary completely intact, and still be
  invisible to an observer — not because it was blocked
  or crowded out, but because the observer lacks the
  right model to decompose it from background.

  THREE CONDITIONS FOR DETECTION (all required):

    1. BASELINE KNOWLEDGE
       The observer must know what is "normal" for THIS node.
       Not a population average — an individual baseline.
       The Parkinson's phone result works because the model
       has longitudinal data on that specific person's voice.
       Population averaging destroys the signal because
       each person's bobber rides on a different background.

    2. PATTERN KNOWLEDGE (the matched basis)
       The observer must know what perturbation geometry
       the hidden cause produces.
       Without this: Parkinson's tremor looks like normal
       voice variation. Fish nibble looks like wind.
       With this: the structure jumps out immediately.
       This is not more statistics — it is a different basis.

    3. TEMPORAL RESOLUTION
       Enough time steps to distinguish the pattern
       from coincidental noise fluctuations.
       Connected to HasVariability T — T must be large
       enough relative to the pattern's period.

  MISSING ANY ONE → signal invisible at boundary
  despite being present and bandwidth-sufficient.

  KEY INSIGHT:
  "Undetectable" is never a property of the signal alone.
  It is always a joint property of:
    signal + observer baseline + observer pattern model + resolution.

  The ASU Parkinson's phone result is an empirical instance:
  the signal was always there in the voice data.
  The bandwidth was sufficient — tremor reached the microphone.
  It looked like noise without the matched basis.
  With the matched basis it was detectable years before
  clinical symptoms — because the causal perturbation
  was already riding on the shadow field of vocal production,
  with sufficient bandwidth to survive to the phone sensor.

  ANALOGY:
  "Can you spot the difference?" puzzles.
  Overlay X[i] with X[i-1] and negate.
  Differences appear plain as day.
  Without the overlay operation: invisible.
  The operation IS the basis choice.
  The bandwidth was always there. The basis was not.
-/

structure ObserverModel where
  /-- Individual baseline for each node -/
  individual_baseline : Node → ℕ → Bool
  /-- Expected perturbation pattern for a given cause -/
  pattern_template    : Node → ℕ → Bool
  /-- Minimum window needed to confirm pattern -/
  min_resolution      : ℕ

/-!
  Basis match: the observer's pattern template aligns
  with the actual perturbation arriving at the boundary.

  When this holds: signal is immediately visible.
  When this fails: signal looks like noise —
  even though bandwidth was sufficient for it to arrive.
-/
def BasisMatched
    (model  : ObserverModel Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (obs    : Node)
    (T      : ℕ) : Prop :=
  T ≥ model.min_resolution ∧
  ∀ t < T,
    DeltaAt Node model.individual_baseline sig obs t ↔
    DeltaAt Node model.individual_baseline
             model.pattern_template obs t

/-!
  DETECTABILITY: delta is present AND observer can see it.

  Both conditions required:
    bandwidth must have been sufficient (delta arrived)
    basis must be matched (observer can decompose it)
-/
def Detectable
    (model  : ObserverModel Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (obs    : Node)
    (T      : ℕ) : Prop :=
  ProducesDelta Node bg sig obs ∧
  BasisMatched Node model bg sig obs T

/-!
  CONJECTURE: matched basis always exists.

  For any structured perturbation that arrives at the
  boundary with sufficient bandwidth, there exists an
  observer model that detects it.

  "Undetectable" is never absolute —
  it is always relative to the current observer model.

  Proved empirically by ASU Parkinson's result:
  the tremor signal had sufficient bandwidth to survive
  to the phone microphone. The matched basis
  (tremor geometry model) made it visible.

  A symmetric bobber signal blends into quantum random
  noise statistically — but in the right basis
  (matched to the signal's symmetry group) it is
  immediately apparent. The basis choice is the
  irreducible representations of the signal's
  symmetry group. Without that group structure:
  looks random. With it: obvious.

  conjecture basis_always_exists :
    ProducesDelta Node bg sig obs →
    ∃ model : ObserverModel Node,
      Detectable Node model bg sig obs T

  Formal proof requires constructive basis existence —
  deferred to future work.
-/


-- ====================================================
-- LAYER 9: BOUNDARY DIFFERENTIAL OPERATORS
-- ====================================================

/-!
  THE "SPOT THE DIFFERENCE" INSIGHT.

  Overlaying X[i] and X[i-1] and negating makes
  differences appear plain as day. Static background
  cancels. Only perturbation remains.

  This is discrete differentiation on the observable
  boundary — the natural detection operator for deltas.

  Connection to bandwidth:
  D₁ detects single delta events — one unit of bandwidth.
  D₂ detects sustained shifts — accumulated bandwidth
  over a window.
  Together they cover both high-frequency and
  low-frequency use of the delta channel.

  TWO OPERATORS detecting different perturbation layers:

    D₁ (first difference, local):
      D₁[i] = X[i] XOR X[i-1]
      Sensitive to SHARP local shifts.
      Detects: Parkinson's tremor, fish nibble,
               sudden market shock, outbreak onset.
      Each spike = one delta event = one bandwidth unit.

    D₂ (windowed average difference, smooth):
      Sensitive to SUSTAINED shifts over a window.
      Detects: cancer incidence drift, NAFTA trade shift,
               slow population-level exposure buildup.
      Accumulated bandwidth over window k.

  THE HALLUCINATION PROBLEM:
  Long enough random noise produces spurious D₁ spikes.
  A random walk occasionally takes a big step.
  This looks like a delta event but consumes bandwidth
  without carrying variability signal.

  THE FIX — structural, not statistical:
  A causal delta has CORRELATED structure across
  multiple boundary nodes simultaneously.
  Bandwidth-carrying random noise hits nodes independently.
  A propagating perturbation hits multiple nodes
  with the same wave front — correlated D₁ spikes,
  consistent direction, synchronized timing.

  One node spiking = bandwidth event, could be noise.
  Five nodes spiking coherently = wave front passing through.
  The correlation IS the evidence.
-/

def D₁
    (sig : TemporalSignal Node)
    (n   : Node)
    (t   : ℕ) : Bool :=
  sig n t != sig n (t - 1)

def LocalSpike
    (sig : TemporalSignal Node)
    (n   : Node)
    (t   : ℕ) : Prop :=
  D₁ Node sig n t = true

/-!
  Coherent delta across a set of boundary nodes:
  multiple nodes spike simultaneously.

  This is what distinguishes a genuine causal wave front
  (correlated bandwidth events) from random noise
  (uncorrelated bandwidth events).
-/
def CoherentDelta
    (sig       : TemporalSignal Node)
    (obs_nodes : Finset Node)
    (t         : ℕ)
    (threshold : ℕ) : Prop :=
  threshold ≤
    (obs_nodes.filter (fun n => LocalSpike Node sig n t)).card

/-!
  Sustained shift: windowed D₂ operator.
  Detects slow drifts invisible to D₁.
  Accumulated bandwidth over window k.
-/
def D₂
    (sig : TemporalSignal Node)
    (n   : Node)
    (t k : ℕ) : Prop :=
  ∃ t₁ t₂,
    t₁ < t ∧ t < t₂ ∧ t₂ ≤ t + k ∧
    sig n t₁ ≠ sig n t₂

/-!
  CAUSAL WAVE FRONT THEOREM.

  If a delta propagates to multiple boundary nodes,
  those nodes show coherent D₁ spikes above threshold.

  The bandwidth events are correlated because they share
  a common hidden source. Random bandwidth events are not.
  This correlation is the structural fingerprint of
  a genuine causal wave front vs hallucination.
-/
theorem causal_propagation_implies_coherent_delta
    (G         : CausalGraph Node)
    (bg        : Background Node)
    (sig       : TemporalSignal Node)
    (source    : Node)
    (obs_nodes : Finset Node)
    (t         : ℕ)
    (h_src     : DeltaAt Node bg sig source t)
    (h_prop    : ∀ n ∈ obs_nodes,
                   PathExists Node G source n ∧
                   DeltaAt Node bg sig n t)
    (h_thresh  : obs_nodes.card > 0) :
    CoherentDelta Node sig obs_nodes t 1 := by
  unfold CoherentDelta
  obtain ⟨n, hn⟩ := Finset.nonempty_of_ne_empty
    (Finset.card_pos.mp h_thresh |>.ne')
  have hspike : LocalSpike Node sig n t := by
    unfold LocalSpike D₁
    have := (h_prop n hn).2
    unfold DeltaAt at this
    simp [Bool.ne_iff_eq_not]
    sorry
    -- bridge between DeltaAt (Prop) and D₁ (Bool)
    -- requires: sig n t ≠ bg n t → sig n t ≠ sig n (t-1)
    -- needs background stability assumption:
    --   bg n t = bg n (t-1) at boundary
    -- deferred: clean with one extra hypothesis
  have hmem : n ∈ obs_nodes.filter
      (fun n => LocalSpike Node sig n t) :=
    Finset.mem_filter.mpr ⟨hn, hspike⟩
  exact Nat.one_le_iff_ne_zero.mpr
    (Finset.card_pos.mpr ⟨n, hmem⟩ |>.ne')

/-!
  THE HALLUCINATION BOUND CONJECTURE.

  Spurious CoherentDelta from uncorrelated noise
  decreases with threshold.

  This is where probability re-enters — but now
  as downstream of bandwidth geometry:

  Uncorrelated noise = no shared causal source =
  no shared bandwidth event = spikes independent.
  Independent spikes hitting threshold simultaneously
  is exponentially unlikely in threshold.

  Correlated causal delta = shared source =
  shared bandwidth event = spikes synchronized.
  Synchronized spikes above threshold is EXPECTED.

  The statistical argument bottoms out in graph geometry:
  correlation structure comes from causal structure,
  not the other way around.

  conjecture hallucination_exponential_decay :
    uncorrelated_noise sig obs_nodes →
    Prob(CoherentDelta sig obs_nodes t threshold) ≤ 2^(-threshold)

  Deferred: requires probability measure on signals,
  which is downstream of causal graph geometry.
-/


-- ====================================================
-- LAYER 10: SUMMARY AND OPEN QUESTIONS
-- ====================================================

/-!
  THE COMPLETE PICTURE.

  PROPAGATION (Layers 1-5):
    Hidden cause has variability
      → delta propagates through causal graph
      → bandwidth budget determines how much survives
      → at boundary: delta present if budget sufficient

  FAILURE MODES (Layer 4):
    SATURATION  — other signals filled the budget
                  channel loud, variability crowded out
                  fingerprint: high BandwidthUsed
    BLOCKING    — bottleneck reduced path_count to zero
                  channel silent, no capacity at all
                  fingerprint: low path_count, detectable
                               as bottleneck in radar file

  ENTROPY CONNECTION (Layer 6):
    High path entropy → budget distributed across many nodes
                      → saturation requires broad coordination
                      → that coordination is itself detectable
    Low path entropy  → budget concentrated at few nodes
                      → saturation or blocking is easy
                      → but the concentration is detectable

  OBSERVER BASIS (Layer 8):
    Delta at boundary detectable iff:
      · individual baseline known (not population avg)
      · pattern model matched to signal's symmetry group
      · sufficient temporal resolution
    "Undetectable" = wrong basis, not absent signal
    ASU Parkinson's: bandwidth sufficient, basis was missing

  BOUNDARY DIFFERENTIALS (Layer 9):
    D₁ catches sharp bandwidth events (high frequency)
    D₂ catches sustained bandwidth shifts (low frequency)
    CoherentDelta across nodes = wave front, not noise
    Hallucination requires correlated noise = causal structure

  OPEN QUESTIONS FOR FUTURE FILES:
    1. Close the sorry in causal_propagation_implies_coherent_delta
       Needs: background stability at boundary + Bool/Prop bridge

    2. Formalize ChannelCapacity with proper path Fintype
       Needs: finite path enumeration on finite graphs

    3. Prove entropy_makes_saturation_costly conjecture
       Needs: PathConcentration summing over paths

    4. Prove basis_always_exists conjecture
       Needs: constructive basis from signal symmetry group
       Connection: irreducible representations of signal's
       symmetry group = the matched basis

    5. Hallucination bound
       Needs: probability measure downstream of graph geometry
       This is a separate file — probability as emergent
       from causal structure, not primitive

  REAL-WORLD ANCHORS:
    ASU Parkinson's phone study    — bandwidth + basis problem
    Kepler mission                 — bandwidth sufficient, basis found
    Testicular cancer / NAFTA      — D₂ sustained shift, bandwidth
                                     competing with demographic noise
    Bobber / fish / perch nibble   — individual baseline + pattern match
    Quantum random string          — symmetric signal, wrong basis,
                                     statistically invisible but
                                     structurally present
    Stellar wobble / dark matter   — bandwidth sufficient,
                                     basis = gravitational geometry
-/

end PerturbationField
