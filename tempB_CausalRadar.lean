/- =====================================================
   Triangle inequality as a hidden-path detector
===================================================== -/

/-
IMPORTANT:

We do NOT assume effectiveDistance is a metric.

We do NOT require the triangle inequality to hold.

Instead, violation of the triangle inequality is itself
an observable finding — it reveals that the hidden
system contains a direct path from A to C that bypasses
B entirely.

When d(A,C) < d(A,B) + d(B,C), the observer has
detected a structural feature of the hidden graph:
a shortcut that makes the induced geometry non-metric.
-/

/-- The triangle inequality may fail for the induced geometry -/
def triangleViolation
    (RK : ResponseKernel OI)
    (a b c : OI.Observable) : Prop :=
  effectiveDistance RK a c 
    effectiveDistance RK a b +
    effectiveDistance RK b c

/-
A triangle violation between A, B, C means:
the expected propagation time from A directly to C
is strictly less than going A→B→C.

This implies the hidden system has a path A→C that
does not route through B — a direct coupling or
privileged channel invisible from B's perspective.
-/

theorem triangle_violation_reveals_bypass
    (RK : ResponseKernel OI)
    (a b c : OI.Observable)
    (h : triangleViolation RK a b c) :
    ∃ δ : ℝ,
      δ > 0 ∧
      effectiveDistance RK a c + δ ≤
        effectiveDistance RK a b +
        effectiveDistance RK b c := by
  unfold triangleViolation at h
  refine ⟨
    effectiveDistance RK a b +
    effectiveDistance RK b c -
    effectiveDistance RK a c,
    by linarith,
    by linarith⟩


/-
Contrapositive reading:

If the observer finds that for ALL intermediaries b,
the triangle inequality holds, then there is no
detectable direct hidden path —
every route goes through at least one known step.

This is the "no hidden shortcut" certificate.
-/

def noHiddenShortcut
    (RK : ResponseKernel OI)
    (a c : OI.Observable) : Prop :=
  ∀ b : OI.Observable,
    effectiveDistance RK a c ≤
      effectiveDistance RK a b +
      effectiveDistance RK b c

/-
Note: noHiddenShortcut does NOT mean the hidden graph
has no direct A→C edge. It means the observer cannot
*detect* one from timing statistics alone.

The epistemics remain bounded: absence of a timing
shortcut is absence of evidence, not evidence of absence.
-/
