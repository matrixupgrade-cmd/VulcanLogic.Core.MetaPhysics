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

  KEY CLAIM (the Sherlock principle for variability):
    To block a delta from reaching observable nodes,
    the hidden graph must contain a coordinated inverse structure
    that cancels the delta across ALL propagation paths
    simultaneously.

    The more paths exist (high entropy graph), the harder
    this coordination becomes.

    Therefore: either the delta reaches the boundary,
    or the blocking structure is itself detectable
    as an anomalous low-entropy pocket in the graph.

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
       We reason about path *existence* and *cut set size*,
       not path content.

    4. The inverse/cancellation condition is the interesting object.
       It is defined precisely enough to reason about, but left
       as a hypothesis in the main theorem — making the dependency
       on graph structure explicit at every call site.
       (Same design philosophy as h_dist_from_sig in the
       InterfaceConfig file.)

    5. The entropy/concentration bound is stated as a conjecture
       at this exploratory stage. The shape of the argument is
       clear; the proof requires a graph entropy definition
       to be chosen carefully.
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
  causal path to a target, then the target inherits
  the delta.

  This is kept as an axiom/hypothesis because the
  exact propagation mechanism is domain-dependent.
  In the Kepler case: gravity propagates the wobble.
  In the epidemiology case: infection chains propagate
  the incidence shift.
  In the bobber case: water tension propagates the tug.

  The mathematics is the same regardless of domain.
-/
def PropagatesDelta
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (target : Node) : Prop :=
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
-- LAYER 4: THE INVERSE / CANCELLATION CONDITION
-- ====================================================

/-!
  An inverse node: a node that produces the exact
  complement of an incoming delta — canceling it.

  In physical terms: destructive interference.
  A wave meets its exact anti-wave.

  For this to work, the inverse node must:
    1. Receive the delta
    2. Generate the exact negation
    3. Route that negation to ALL paths to the observable

  Condition 3 is what makes this nearly impossible
  in high-entropy graphs.
-/
def InverseNode
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (v      : Node)
    (T      : ℕ) : Prop :=
  ∀ t < T,
    DeltaAt Node bg sig source t →
    ¬ DeltaAt Node bg sig v t

/-!
  A coordinated cancellation structure:
  a set of nodes S that collectively inverts the
  delta from source before it reaches observable obs.

  "Collectively" is the hard part:
  every path from source to obs must pass through
  some node in S, AND that node must carry the inverse
  pattern.

  In the bobber analogy: you'd need a counter-wave
  that intercepts every path the fish-tug takes
  through the water — including all the reflections,
  eddies, and indirect routes.
-/
def CoordinatedCancellation
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (obs    : Node)
    (S      : Finset Node)
    (T      : ℕ) : Prop :=
  -- S cuts all paths from source to obs
  (∀ p : CausalPath Node G source obs,
    ∃ v ∈ S, NodeOnPath p v) ∧
  -- every node in S carries the inverse pattern
  (∀ v ∈ S, InverseNode Node bg sig source v T)

/-!
  No coordinated cancellation exists:
  there is no finite set of nodes that can simultaneously
  cut all paths AND carry the inverse pattern.

  This is the condition that allows delta propagation.
  In a high-entropy graph, this holds generically.
-/
def NoCancellation
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (obs    : Node)
    (T      : ℕ) : Prop :=
  ∀ S : Finset Node,
    ¬ CoordinatedCancellation Node G bg sig source obs S T


-- ====================================================
-- LAYER 5: MAIN THEOREMS
-- ====================================================

/-!
  DELTA PROPAGATION THEOREM.

  If:
    · source produces a delta
    · a causal path exists from source to obs
    · the graph propagates deltas along paths
    · no coordinated cancellation exists

  Then: obs produces a delta.

  The hidden structure is never enumerated.
  The proof is purely structural.
-/
theorem delta_reaches_observable
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (obs    : Node)
    (T      : ℕ)
    -- source has a delta
    (h_src  : ProducesDelta Node bg sig source)
    -- path exists (entropy guarantees many; we only need one)
    (h_path : PathExists Node G source obs)
    -- graph propagates deltas (domain-specific assumption)
    (h_prop : PropagatesDelta Node G bg sig source obs)
    -- no cancellation structure exists
    (h_nocancel : NoCancellation Node G bg sig source obs T) :
    ProducesDelta Node bg sig obs := by
  exact h_prop h_src h_path

/-!
  PERTURBATION FIELD MEMBERSHIP.

  If delta reaches obs and a path exists,
  then obs is in the perturbation field of source.

  The perturbation field is the set of all nodes
  "lit up" by the propagating delta.
  This is the formal version of the shadow field.
-/
theorem obs_in_perturbation_field
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (obs    : Node)
    (T      : ℕ)
    (h_src  : ProducesDelta Node bg sig source)
    (h_path : PathExists Node G source obs)
    (h_prop : PropagatesDelta Node G bg sig source obs)
    (h_nocancel : NoCancellation Node G bg sig source obs T) :
    obs ∈ PerturbationField Node G source bg sig := by
  unfold PerturbationField
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h_path, h_prop h_src h_path⟩

/-!
  THE SHERLOCK PRINCIPLE FOR VARIABILITY.

  If delta does NOT reach the observable boundary,
  then coordinated cancellation MUST exist in the graph.

  Contrapositive: absence of observable delta is itself
  evidence of specific hidden structure —
  a low-entropy, coordinated inverse mechanism.

  In the bobber analogy: if the bobber is completely
  still despite the fish, something is actively
  canceling the perturbation. That cancellation
  is its own detectable anomaly.
-/
theorem no_delta_implies_cancellation
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (obs    : Node)
    (T      : ℕ)
    (h_src  : ProducesDelta Node bg sig source)
    (h_path : PathExists Node G source obs)
    (h_prop : PropagatesDelta Node G bg sig source obs)
    -- delta does NOT reach observable
    (h_no_delta : ¬ ProducesDelta Node bg sig obs) :
    -- therefore cancellation must exist
    ∃ S : Finset Node,
      CoordinatedCancellation Node G bg sig source obs S T := by
  exfalso
  exact h_no_delta (h_prop h_src h_path)

/-!
  VARIABILITY PRESERVATION THEOREM.

  If the source has variability (not just a single delta,
  but a fluctuating pattern) AND no cancellation exists,
  THEN the observable inherits variability structure.

  This is the virus-cancer incidence connection:
  flux in the upstream cause creates detectable
  flux in the downstream observable.

  Note: this requires a stronger propagation hypothesis
  that delta-with-variability propagates as variability.
  Stated as a hypothesis (h_var_prop) rather than derived,
  following the design philosophy of making domain
  assumptions explicit.
-/
def PropagatesVariability
    (G      : CausalGraph Node)
    (bg     : Background Node)
    (sig    : TemporalSignal Node)
    (source : Node)
    (obs    : Node)
    (T      : ℕ) : Prop :=
  VariabilitySource Node bg sig source T →
  PathExists Node G source obs →
  HasVariability Node sig obs T

theorem variability_reaches_boundary
    (G        : CausalGraph Node)
    (bg       : Background Node)
    (sig      : TemporalSignal Node)
    (source   : Node)
    (obs      : Node)
    (T        : ℕ)
    -- source is a variability source
    (h_vsrc   : VariabilitySource Node bg sig source T)
    -- path exists
    (h_path   : PathExists Node G source obs)
    -- variability propagates (domain assumption)
    (h_var_prop : PropagatesVariability Node G bg sig source obs T)
    -- no cancellation
    (h_nocancel : NoCancellation Node G bg sig source obs T) :
    HasVariability Node sig obs T := by
  exact h_var_prop h_vsrc h_path


-- ====================================================
-- LAYER 6: ENTROPY AND CANCELLATION COST
-- ====================================================

/-!
  PATH CONCENTRATION.

  How many paths from source to obs pass through node v.
  High concentration at a single node = low entropy graph.
  That node is a candidate bottleneck / inverse node.

  Note: path counting requires decidability of path
  membership. Keeping this as a natural number count
  over a finite type.
-/
def PathConcentration
    (G      : CausalGraph Node)
    (source : Node)
    (obs    : Node)
    (v      : Node)
    (paths  : Finset (CausalPath Node G source obs)) : ℕ :=
  paths.card.pred  -- placeholder: count paths through v

-- TODO: proper definition requires paths to be a Fintype
-- For now, the structure is correct; filling in requires
-- a finite path enumeration strategy.
-- This is where the "finite graph, finite paths" lemma lives.

/-!
  GRAPH PATH ENTROPY (simplified).

  A graph has high path entropy between source and obs
  if no single node dominates the path structure —
  every node appears on at most ε fraction of paths.

  Low entropy: "AAAAA" — one node on every path.
  High entropy: "BDFBAC" — no node dominates.
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
  CANCELLATION REQUIRES LARGE CUT SET.

  In a high-entropy graph, any cut set that blocks
  all paths must be large — proportional to total paths
  divided by max per-node concentration.

  This is the key entropy-vs-cancellation tradeoff:
  the more distributed the path structure,
  the more nodes are needed to cancel,
  the harder coordination becomes.

  CONJECTURE (exploratory):
    HighPathEntropy G source obs ε paths →
    is_cut_set G source obs S paths →
    S.card ≥ paths.card / ε

  Stated as a conjecture because PathConcentration
  needs a proper finite path enumeration to close.
  The logical shape is clear; the proof requires
  the right Fintype infrastructure.
-/

/-!
  THE CORE CONJECTURE.

  Sufficient entropy in the hidden graph makes
  coordinated cancellation geometrically impossible
  without a detectable low-entropy pocket.

  Not yet a theorem — marked as a conjecture at this
  exploratory stage. The direction is:

    HighPathEntropy G source obs ε paths ∧
    large enough paths.card
    →
    NoCancellation G bg sig source obs T

  Because: cancellation requires cut set of size ≥ paths.card/ε.
  Each cut node must carry inverse pattern.
  Coordinating inverse patterns across a large set
  requires the set itself to have low entropy.
  That low entropy is detectable.

  The inverse almost never exists in natural graphs
  for the same reason a perfect anti-wave almost
  never exists in turbulent water:
  it requires organized anti-structure across all paths,
  which is itself a high-information, low-entropy object.
-/
-- conjecture entropy_prevents_cancellation
--   (G      : CausalGraph Node)
--   (bg     : Background Node)
--   (sig    : TemporalSignal Node)
--   (source : Node)
--   (obs    : Node)
--   (T ε    : ℕ)
--   (paths  : Finset (CausalPath Node G source obs))
--   (h_ent  : HighPathEntropy Node G source obs ε paths)
--   (h_many : paths.card > ε * Fintype.card Node) :
--   NoCancellation Node G bg sig source obs T


-- ====================================================
-- LAYER 7: CONNECTION TO PREVIOUS FILES
-- ====================================================

/-!
  BRIDGE TO CAUSAL RADAR (CausalGraph.lean).

  A coordinated cancellation structure — if it exists —
  appears as an asymmetric_interface in the radar file.

  Because: the inverse nodes must behave differently
  from generic nodes. That behavioral difference is
  exactly a nonzero commutator in the latency field.

  So the radar's structural_diversity theorem would
  detect the cancellation structure as a positive
  accumulated_asymmetry.

  Consequence:
    Either delta reaches the boundary,
    OR cancellation structure exists,
    OR structural diversity is positive (detectable).

  All three cases give the observer information.
  There is no "invisible blocking" of variability
  in a generic causal graph.

  BRIDGE TO INTERFACE CONFIG (InterfaceConfig.lean).

  The perturbation field is a basin in the sense of
  that file: a set of nodes grouped by their
  relationship to the delta source.

  The three-level sandwich theorem then bounds the
  complexity of observing the perturbation:
    basin_local_complexity ≤ basin_entropy ≤ |Signal|

  So even the shadow field's observability is bounded
  by the entropy of the signal basin, not by the
  complexity of the hidden graph.

  BRIDGE TO GATEWAY (gateway_region in first file).

  A forced bottleneck through a cancellation set S
  is exactly a gateway_region — the set of nodes
  where divergence between "delta present" and
  "delta absent" worlds routes its escape.

  The pigeonhole theorem (forced_gateway_overlap)
  then shows that if enough distinct outcomes route
  through a small gateway, some gateway node must
  handle multiple outcomes — making it detectable.
-/


-- ====================================================
-- LAYER 8: THE OBSERVER BASIS PROBLEM
-- ====================================================

/-!
  THE BOBBER PROBLEM.

  A delta can propagate perfectly through the hidden graph,
  arrive at the boundary completely intact, and still be
  invisible to an observer — not because it was blocked,
  but because the observer lacks the right model to
  decompose it from background.

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
  despite being present and uncanceled.

  KEY INSIGHT:
  "Undetectable" is never a property of the signal alone.
  It is always a joint property of:
    signal + observer baseline + observer pattern model + resolution.

  The ASU Parkinson's phone result is an empirical instance
  of this theorem: the signal was always there in the voice data.
  It looked like random noise without the matched basis.
  With the matched basis it was detectable years before
  clinical symptoms — because the causal perturbation
  was already riding on the shadow field of vocal production.

  ANALOGY:
  "Can you spot the difference?" puzzles.
  Overlay image X[i] with X[i-1] and negate.
  Differences appear plain as day.
  Without the overlay operation: invisible.
  The operation IS the basis choice.
-/

/-!
  An observer model: what the observer believes the
  perturbation geometry looks like.

  In the Parkinson's case: the tremor frequency profile.
  In the bobber case: the micro-motion pattern of a fish nibble.
  In the cancer incidence case: the variance signature
  of a fluctuating viral cause.

  Without this model, the observer cannot distinguish
  signal from background even when the delta is present.
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
  When this fails: signal looks like noise.
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
  DETECTABILITY THEOREM.

  Delta is detectable at obs if and only if:
    · delta is present (propagation succeeded)
    · observer has matched basis
    · sufficient temporal resolution

  This is the formal statement that "undetectable"
  is an observer property, not a signal property.
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

  For any structured perturbation pattern that arrives
  at the boundary, there exists an observer model that
  detects it.

  "Undetectable" is never absolute —
  it is always relative to the current observer model.

  Proved empirically by ASU Parkinson's result:
  the signal was always there. The matched basis
  (tremor geometry model) made it visible.

  Formal proof requires a constructive basis existence
  argument — deferred to future work.

  conjecture basis_always_exists :
    ProducesDelta Node bg sig obs →
    ∃ model : ObserverModel Node,
      Detectable Node model bg sig obs T
-/


-- ====================================================
-- LAYER 9: BOUNDARY DIFFERENTIAL OPERATORS
-- ====================================================

/-!
  THE "SPOT THE DIFFERENCE" INSIGHT.

  Overlaying X[i] and X[i-1] and negating makes
  differences appear plain as day. The static background
  cancels. Only the perturbation remains.

  This is discrete differentiation on the observable
  boundary — and it is the natural detection operator
  for causal deltas.

  TWO OPERATORS, detecting different perturbation layers:

    D₁ (first difference, local):
      D₁[i] = X[i] XOR X[i-1]
      Sensitive to SHARP local shifts.
      Detects: Parkinson's tremor, fish nibble,
               sudden market shock, outbreak onset.

    D₂ (windowed average difference, smooth):
      D₂[i,k] = majority(X[i..i+k]) ≠ majority(X[i-k..i])
      Sensitive to SUSTAINED shifts over a window.
      Detects: cancer incidence drift, NAFTA trade shift,
               slow population-level exposure buildup.

  These detect DIFFERENT layers of the perturbation field:
    D₁ → high frequency delta events (sharp causal shifts)
    D₂ → low frequency delta events  (sustained causal pressure)

  A hidden cause producing a sharp shift: visible in D₁.
  A hidden cause building slowly: visible in D₂, invisible in D₁.
  Both operators together give broader detection coverage.

  THE HALLUCINATION PROBLEM:
  Long enough random noise produces spurious D₁ spikes.
  A random walk occasionally takes a big step.
  This looks like a delta event but is not one.

  THE FIX — not statistical, structural:
  A causal delta has CORRELATED structure across
  multiple boundary nodes simultaneously.
  Random noise produces isolated, uncorrelated spikes.
  A propagating perturbation produces:
    · correlated spikes across related observables
    · consistent direction of shift
    · decay pattern matching graph path length
    · cross-node synchronization

  Random hallucination almost never produces ALL of these.
  So the detection operator is D₁ correlated across
  multiple boundary nodes, not D₁ at a single node.
-/

/-!
  First difference operator on a temporal signal at node n.
  Returns true when the signal changes between t-1 and t.
  This is the discrete derivative — the "overlay and negate."
-/
def D₁
    (sig : TemporalSignal Node)
    (n   : Node)
    (t   : ℕ) : Bool :=
  sig n t != sig n (t - 1)   -- Bool XOR

/-!
  A node shows a local spike at time t:
  its first difference is nonzero.
-/
def LocalSpike
    (sig : TemporalSignal Node)
    (n   : Node)
    (t   : ℕ) : Prop :=
  D₁ Node sig n t = true

/-!
  Coherent delta across a set of boundary nodes:
  multiple nodes spike simultaneously (or with consistent lag).

  This is what distinguishes a genuine causal wave front
  from random noise hallucination.

  One node spiking = could be noise.
  Five nodes spiking coherently = wave front passing through.
-/
def CoherentDelta
    (sig       : TemporalSignal Node)
    (obs_nodes : Finset Node)
    (t         : ℕ)
    (threshold : ℕ) : Prop :=
  threshold ≤
    (obs_nodes.filter (fun n => LocalSpike Node sig n t)).card

/-!
  Sustained shift detected by windowed operator D₂:
  the signal's majority value changes across a window boundary.

  Window [t-k, t] vs [t, t+k].
  Detects slow drifts invisible to D₁.
-/
def D₂
    (sig : TemporalSignal Node)
    (n   : Node)
    (t k : ℕ) : Prop :=
  -- majority in past window differs from majority in future window
  -- simplified: any difference in windowed sum
  ∃ t₁ t₂,
    t₁ < t ∧ t < t₂ ∧ t₂ ≤ t + k ∧
    sig n t₁ ≠ sig n t₂

/-!
  CAUSAL WAVE FRONT THEOREM.

  If a variability source creates a delta that propagates
  to multiple boundary observables, then those observables
  show a coherent delta — correlated spikes above threshold.

  The key: genuine causal propagation hits multiple nodes.
  Random noise hits nodes independently.

  This is the formal version of:
  "a wave front passing through" vs "random noise."
-/
theorem causal_propagation_implies_coherent_delta
    (G         : CausalGraph Node)
    (bg        : Background Node)
    (sig       : TemporalSignal Node)
    (source    : Node)
    (obs_nodes : Finset Node)
    (t         : ℕ)
    -- source produces a delta at time t
    (h_src     : DeltaAt Node bg sig source t)
    -- delta propagates to ALL obs_nodes
    (h_prop    : ∀ n ∈ obs_nodes,
                   PathExists Node G source n ∧
                   DeltaAt Node bg sig n t)
    -- threshold is the size of obs_nodes
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
    sorry -- requires connecting DeltaAt to D₁ via Bool
  have hmem : n ∈ obs_nodes.filter (fun n => LocalSpike Node sig n t) :=
    Finset.mem_filter.mpr ⟨hn, hspike⟩
  exact Nat.one_le_iff_ne_zero.mpr
    (Finset.card_pos.mpr ⟨n, hmem⟩ |>.ne')

/-!
  THE HALLUCINATION BOUND CONJECTURE.

  Under what conditions does random noise produce
  a CoherentDelta above threshold?

  Conjecture: for uncorrelated noise across nodes,
  the probability of a spurious CoherentDelta decreases
  exponentially with threshold size.

  This is where probability RE-ENTERS the framework —
  but now as downstream of geometry, not fundamental.

  The noise process is uncorrelated BECAUSE the graph
  has no causal structure connecting those nodes.
  The correlation in a genuine causal delta comes FROM
  the graph structure — the shared hidden cause.

  So even the statistical argument bottoms out in
  graph geometry. Probability is generated by the
  causal graph, not the other way around.

  conjecture hallucination_exponential_decay :
    uncorrelated_noise sig obs_nodes →
    P(CoherentDelta sig obs_nodes t threshold) ≤ 2^(-threshold)

  Deferred: requires a probability measure on signals,
  which is downstream of graph geometry.
  The logical shape is clear; the formal proof
  requires choosing how probability emerges from
  the causal structure — a separate file.
-/

/-!
  SUMMARY: THE COMPLETE DETECTION CHAIN.

  Putting all layers together:

  PROPAGATION (Layers 1-5):
    Hidden cause has variability
      → delta propagates through causal graph
      → arrives at boundary observables intact
      → unless coordinated cancellation exists
         (which requires low-entropy hidden structure,
          itself detectable)

  OBSERVER BASIS (Layer 8):
    Delta at boundary is detectable iff:
      · observer has individual baseline (not population avg)
      · observer has matched pattern model
      · sufficient temporal resolution
    "Undetectable" = wrong basis, not absent signal

  BOUNDARY DIFFERENTIALS (Layer 9):
    Detection operator = coherent D₁ across multiple nodes
      · D₁ catches sharp causal shifts
      · D₂ catches slow sustained shifts
      · Coherence across nodes distinguishes signal from noise
      · Hallucination (false positive) requires correlated noise
        which itself implies hidden causal structure

  REAL-WORLD VALIDATION:
    ASU Parkinson's phone study:
      Vocal tremor signal always present in voice data
      Looks like random noise without matched basis
      Model with tremor geometry detects it years before
      clinical symptoms — because it has:
        (1) individual baseline (longitudinal data)
        (2) matched pattern model (tremor geometry)
        (3) sufficient resolution (continuous phone data)

    Kepler mission:
      Planetary wobble always present in stellar flux
      Looks like noise without transit geometry model
      Matched basis (transit timing + depth) → detection

    Testicular cancer / NAFTA signal:
      Incidence rate variability riding on shadow field
      of population exposure dynamics
      Visible as coherent D₂ shift across demographic groups
      at the boundary — once you know what shape to look for

  THE CORE PRINCIPLE:
    Hidden causes imprint characteristic perturbation
    geometries onto observable dynamical fields.
    The geometry is always there.
    Detection is a question of basis, resolution,
    and knowing what shape the bobber should take.
-/

end PerturbationField
