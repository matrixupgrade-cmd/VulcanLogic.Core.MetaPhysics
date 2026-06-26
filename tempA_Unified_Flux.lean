/-!
===============================================================================
Unified_Flux — Telescoping Friction + Where Curl Can Actually Live
Author: Sean Timothy
Revision: Claude (Sonnet 4.6), 2026-06-26
Status: Hand-checked, NOT compiler-verified (same toolchain limitation as
        UnifiedFluxDynamics — please `lake build` and report errors back).

WHAT THIS FILE IS
-------------------------------------------------------------------------------
Part 1 (Telescoping) fixes a real bug in the original: `step_iterate i x` was
called with `step` missing throughout the definition and the lemma statement,
while the *proof* of that same lemma correctly wrote `step_iterate step i x`.
That inconsistency is the same "patched without ever compiling" signature as
the other files — here it's purely structural, so the fix is to thread `step`
explicitly everywhere, and to use Mathlib's own `Function.iterate` (`f^[n]`)
instead of reinventing it.

Part 2 (Holonomy) is the actual answer to "what distinguishes flux from
tension, and am I just dressing tension up in a new outfit?"

THE ANSWER, IN ONE LINE
-------------------------------------------------------------------------------
`total_friction_identity` below is proved for a *commutative* group, and a
commutative group can never have nonzero circulation around a closed loop —
that's not a limitation of this proof, it's what commutativity *means*.
Telescoping cancellation is exactly the statement "it doesn't matter what
order you compose the steps in," and that's also exactly the statement
"there's no curl." So as long as `friction` lives in a CommGroup, this file
can describe tension (how hard something pulls) but can never produce
flux/curl (whether two pulls interfere depending on order) — not because
something's missing, but because the only thing curl could be built from was
removed by assumption.

Part 2 shows where curl actually has to live: in whether two basins' local
pulls *commute*. Model a basin's pull as left-translation by a fixed group
element (its "characteristic displacement"); composing two basins' pulls in
opposite orders differs by exactly the product `a*b*a⁻¹*b⁻¹` — the classical
group commutator of their displacements — independent of the state. That
product is forced to be the identity in a CommGroup (proved below), and is
generically nonzero the moment commutativity is dropped. That's the precise
sense in which "two basins competing for the same trajectory" is a different
question from "how hard is each basin pulling": it's a question about
order-dependence that tension alone can't even ask.
===============================================================================
-/

import Mathlib

universe u

/-! # Part 1: Telescoping friction (fixed) -/

section Telescoping

variable {α : Type u} [CommGroup α]

/-- How much group-displacement one application of `step` adds, starting
from `y`. -/
def friction (step : α → α) (y : α) : α := step y * y⁻¹

/-- A length-`n` closed cycle through `x` under `step`. -/
structure Basin (step : α → α) (x : α) where
  n  : ℕ
  hn : 0 < n
  stabilized : step^[n] x = x

/-- General fact: folding `fun i acc => g i * acc` from an arbitrary starting
accumulator `c` is the same as folding from `1` and multiplying by `c` at the
end. Pure associativity — no commutativity needed for this part. -/
theorem foldr_mul_const {ι : Type*} (g : ι → α) (l : List ι) :
    ∀ c, l.foldr (fun i acc => g i * acc) c
       = (l.foldr (fun i acc => g i * acc) 1) * c := by
  induction l with
  | nil => intro c; simp
  | cons a l ih => intro c; simp [ih, mul_assoc]

/-- Product of friction terms along one full pass of the cycle. -/
def totalFriction (step : α → α) {x : α} (basin : Basin step x) : α :=
  (List.range basin.n).foldr (fun i acc => friction step (step^[i] x) * acc) 1

/-- The telescoping identity itself. -/
theorem foldr_friction_telescopes (step : α → α) (x : α) (m : ℕ) :
    (List.range m).foldr (fun i acc => friction step (step^[i] x) * acc) 1
      = step^[m] x * x⁻¹ := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldr_append]
    have hsingle :
        (List.foldr (fun i acc => friction step (step^[i] x) * acc) 1 [k])
          = friction step (step^[k] x) := by simp
    rw [hsingle, foldr_mul_const, ih]
    unfold friction
    rw [← Function.iterate_succ_apply']
    -- (step^[k] x * x⁻¹) * (step^[k+1] x * (step^[k] x)⁻¹) = step^[k+1] x * x⁻¹
    -- This step genuinely needs commutativity — `group` tactic alone would
    -- NOT close it, since `group` only uses the group axioms, not mul_comm.
    -- That gap is the entire point of Part 2. This is also, of every tactic
    -- call in this file, the one I'd bet on needing a tweak if `simp` doesn't
    -- find the right normal form on the first try.
    simp [mul_comm, mul_assoc, mul_left_comm]

/-- Total friction around any stabilized cycle is the identity: zero net
circulation, always, with no exceptions — as long as `α` is commutative. -/
theorem total_friction_identity (step : α → α) {x : α} (basin : Basin step x) :
    totalFriction step basin = 1 := by
  unfold totalFriction
  rw [foldr_friction_telescopes, basin.stabilized]
  simp

end Telescoping

/-! # Part 2: Holonomy — where curl actually has to live -/

section Holonomy

variable {α : Type u} [Group α]

/-- A basin modeled at its simplest: pulling every state by a fixed
"characteristic displacement" `a`. -/
def translateStep (a : α) : α → α := fun y => a * y

/-- Composing two basins' pulls in opposite orders differs by exactly the
product `a*b*a⁻¹*b⁻¹` — the classical group commutator of their
displacements (conventions for which order to write this in vary across
sources, including Mathlib's own `⁅·,·⁆` notation, so it's spelled out
explicitly here rather than risk a convention mismatch). This holds in ANY
group — no commutativity used in the proof — and is independent of the
state `x`. This is the mechanism that magnitude-based overlap measures
(`discreteCurl`-style scalars) can only ever be a downstream proxy for. -/
theorem holonomy_translateStep (a b x : α) :
    translateStep a (translateStep b x) * (translateStep b (translateStep a x))⁻¹
      = a * b * a⁻¹ * b⁻¹ := by
  unfold translateStep
  group

/-- In a commutative group, two basins' pulls always commute as operations —
not just "some derived quantity happens to be trivial," but literally:
applying A-then-B lands on the same state as B-then-A, for every state. This
is why Part 1's whole world can never host curl: it assumed exactly this. -/
theorem translateStep_comm {β : Type u} [CommGroup β] (a b x : β) :
    translateStep a (translateStep b x) = translateStep b (translateStep a x) := by
  unfold translateStep
  rw [mul_left_comm]

theorem holonomy_translateStep_comm {β : Type u} [CommGroup β] (a b x : β) :
    translateStep a (translateStep b x) * (translateStep b (translateStep a x))⁻¹ = 1 := by
  rw [translateStep_comm]
  simp

end Holonomy

/-!
===============================================================================
Where this leaves things

- Part 1, fixed: telescoping is real, but it's a conservation law (net
  circulation around a closed loop is always zero), not a source of flux.
  It tells you what "no curl" looks like — necessary scaffolding, not the
  payoff, and not something to keep trying to extract curl from.

- Part 2: curl is a question about whether two basins' local actions
  commute, made precise as a group commutator, completely independent of
  capture or membership. `translateStep` is the simplest possible model of
  "a basin's pull" — literally just left-translation — and it already shows
  the whole structural point: commutativity (Part 1's entire world) forces
  the commutator to vanish; dropping it doesn't.

- Deliberately not attempted here: connecting `translateStep`/the commutator
  back to the actual `ObservedDynamics`/`FluxField` machinery from
  UnifiedFluxDynamics_v3 — i.e. what group `α` should even be for a real
  dynamic-NN trajectory, and what "basin pull" corresponds to concretely (a
  logit direction? a local Jacobian? something else). That's the next real
  design decision, and it's worth getting right before formalizing it rather
  than guessing at it here.
===============================================================================
-/
