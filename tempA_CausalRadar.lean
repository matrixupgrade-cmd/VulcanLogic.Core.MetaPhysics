import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.NormedSpace.Basic

open scoped BigOperators

set_option autoImplicit false

universe u

/-!
=========================================================
CAUSAL RADAR SYSTEMS
---------------------------------------------------------

Core idea:

Observable nodes emit demand signals into a hidden
causal geometry.

The observer cannot directly access:
- hidden topology
- hidden routing
- hidden coupling structure

The observer only sees:
- emitted demand waves
- returned supply responses
- propagation timing statistics

From this, an *emergent effective geometry* is inferred.
=========================================================
-/

/- =====================================================
   Hidden causal system
===================================================== -/

structure HiddenSystem where
  Node : Type u
  edge : Node → Node → Prop


/- =====================================================
   Observable interface
===================================================== -/

structure ObservableInterface (HS : HiddenSystem) where
  Observable : Type u
  embed : Observable → HS.Node


/- =====================================================
   Demand / supply signals
===================================================== -/

structure DemandSignal (HS : HiddenSystem) (OI : ObservableInterface HS) where
  src : OI.Observable
  issued_at : ℝ

structure SupplyResponse (HS : HiddenSystem) (OI : ObservableInterface HS) where
  dst : OI.Observable
  arrived_at : ℝ


structure PropagationEvent (HS : HiddenSystem)
    (OI : ObservableInterface HS) where
  demand : DemandSignal HS OI
  response : SupplyResponse HS OI


/- =====================================================
   Observable timing
===================================================== -/

def propagationDelay
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (e : PropagationEvent HS OI) : ℝ :=
  e.response.arrived_at - e.demand.issued_at


/-
=========================================================
Propagation kernel (radar image)
=========================================================
-/

abbrev TimeDistribution := ℝ → ℝ  -- simplified placeholder

structure ResponseKernel (HS : HiddenSystem)
    (OI : ObservableInterface HS) where
  K : OI.Observable → OI.Observable → TimeDistribution


noncomputable
def expectedTime
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (a b : OI.Observable) : ℝ :=
  ∑' t, t * RK.K a b t


/- =====================================================
   Emergent effective geometry
===================================================== -/

noncomputable
def effectiveDistance
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (a b : OI.Observable) : ℝ :=
  expectedTime HS OI RK a b


/- =====================================================
   Triangle structure (CRITICAL ADDITION)
===================================================== -/

/-
We do NOT assume triangle inequality holds.

We DEFINE its violation as a measurable signal.
-/

def triangleDefect
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (a b c : OI.Observable) : ℝ :=
  effectiveDistance HS OI RK a b +
  effectiveDistance HS OI RK b c -
  effectiveDistance HS OI RK a c


def triangleViolation
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (a b c : OI.Observable) : Prop :=
  triangleDefect HS OI RK a b c > 0


/-!
Interpretation:

triangleViolation means:

A → C is faster than A → B → C

This suggests:
- hidden shortcut
- privileged routing
- non-compositional propagation
- structural bypass in hidden geometry
-/


/- =====================================================
   Observations
===================================================== -/

structure Observation (HS : HiddenSystem)
    (OI : ObservableInterface HS) where
  src : OI.Observable
  dst : OI.Observable
  observed_delay : ℝ


noncomputable
def timingDeviation
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (obs : Observation HS OI) : ℝ :=
  obs.observed_delay -
    effectiveDistance HS OI RK obs.src obs.dst


def fastAnomaly
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (threshold : ℝ)
    (obs : Observation HS OI) : Prop :=
  timingDeviation HS OI RK obs < -threshold


def slowAnomaly
    (HS : HiddenSystem) (OI : ObservableInterface HS)
    (RK : ResponseKernel HS OI)
    (threshold : ℝ)
    (obs : Observation HS OI) : Prop :=
  timingDeviation HS OI RK obs > threshold


/- =====================================================
   Causal radar interpretation
===================================================== -/

/-
Key idea:

Demand = injected wave
Supply = returned echo

Hidden system acts as propagation medium:
- it distorts timing
- it induces effective geometry
- it creates non-metric structure

Observers reconstruct geometry ONLY from:
- arrival times
- variance patterns
- triangle defects
- statistical propagation
-/


/- =====================================================
   Epistemic principle
===================================================== -/

/-
We do NOT observe hidden topology.

We observe propagation distortion.

Geometry is inferred, not assumed.
-/


/- =====================================================
   Future extensions
===================================================== -/

/-
Natural next steps:

- probabilistic triangle defect (variance-aware)
- spectral decomposition of ResponseKernel
- curvature field over observables
- multi-scale radar reconstruction
- Bayesian hidden geometry inference
- random walk propagation models
- entropy of causal flow

Core idea remains:

    geometry = emergent from propagation statistics
-/
