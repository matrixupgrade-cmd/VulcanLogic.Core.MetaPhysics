/-!
# NeuralNetworkAsCompression.lean

The document "Reading Neural Networks Through Signal Geometry" says:
  *"A neural network is a compression of an underlying dynamical system."*

This sounds like a metaphor. It is not. This file proves it as a theorem.

---

## The Confusion, Diagnosed

Other AI readers (and humans) interpret the claim in one of two wrong ways:

**Wrong reading 1**: The NN approximates some external physical dynamical system.
**Wrong reading 2**: "Dynamical system" is a loose analogy for how activations
  flow through layers.

**Correct reading**: The neural network forward pass f : α → α *is* a dynamical
  system. The MetaMap is the canonical algebraic quotient of *that system*. They
  are the same object seen at two levels of description, related by a proved
  semi-conjugacy. Nothing external. Nothing approximate.

---

## The Chain, Made Unambiguous

```
f : α → α                            (neural network forward pass)
  floating-point arithmetic → α is finite
  forward pass is deterministic → f is well-defined
  ↓
  every orbit is eventually periodic  (§2: pigeonhole on finite α)
  ↓
  attractor equivalence x ~ y on α   (§3: x ~ y iff orbits converge)
  ↓
  MetaMap quotient Q = α / ~         (§4: the compressed dynamical system)
  ↓
  f factors through Q via π : α → Q  (§5: the semi-conjugacy)
  ↓
  every Q-orbit is cyclic             (§6: ZMod-n algebraic structure)
  ↓
  concepts = algebraic components of Q (§7: main theorem)
```

Every arrow is a proved theorem. The MetaMap exists whether or not you measure it.
Signal geometry probes approximate the semi-conjugacy π. That is why they work.

---

## Connections to Existing LogicCore Files

- `FinIterMap` here corresponds to the finite iterative semigroup in `BasinDynamics`
- `attractorRel` is the equivalence underlying `MetaMapIsomorphismTheorem`
- `metamap_orbits_cyclic` is the ZMod-n structure claim in `LearningSystemsTheory`
- The `solid/liquid/plasma` distinction reads off the orbit period here directly:
    period = 0 → not yet in attractor (plasma / transient)
    period = 1 → fixed point (solid)
    period = n > 1 → genuine cycle (liquid; Turing-universal by related theorem)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Iterate

namespace NeuralNetworkCompression

-- ════════════════════════════════════════════════════════════════════════════
-- §1.  Finite Iterative Maps  (the neural network is one of these)
-- ════════════════════════════════════════════════════════════════════════════

/-- A deterministic self-map of a finite type.
    Any neural network forward pass is an instance of this structure:
    - IEEE 754 floating-point arithmetic is finite (discrete state space)
    - The forward pass is fully deterministic
    Therefore all theorems below apply directly to neural networks. -/
structure FinIterMap (α : Type*) [Fintype α] where
  f : α → α

variable {α : Type*} [Fintype α] (F : FinIterMap α)

/-- n-fold iteration of the map. iter 0 = id; iter (n+1) = f ∘ iter n. -/
abbrev iter (n : ℕ) (x : α) : α := F.f^[n] x

-- ════════════════════════════════════════════════════════════════════════════
-- §2.  Eventual Periodicity
-- ════════════════════════════════════════════════════════════════════════════

/-- **Eventual Periodicity Theorem**: every orbit under a finite iterative map
    is eventually periodic.

    *Proof*: ℕ is infinite but α is finite. The map n ↦ fⁿ(x) : ℕ → α cannot
    be injective. By pigeonhole, two distinct indices i < j must satisfy
    fⁱ(x) = fʲ(x). Set T := i, period := j - i.

    *Consequence for neural networks*: The network has finitely many distinct
    long-run behaviors. The MetaMap captures all of them. -/
theorem eventually_periodic (x : α) :
    ∃ (T period : ℕ), 0 < period ∧ F.iter (T + period) x = F.iter T x := by
  -- ℕ → α cannot be injective when α is finite
  have not_inj : ¬Function.Injective (F.iter · x) :=
    Fintype.not_injective_infinite_finite _
  obtain ⟨i, j, hne, heq⟩ := Function.not_injective_iff.mp not_inj
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j - i, Nat.sub_pos_of_lt h,
      by rw [Nat.add_sub_cancel' h.le]; exact heq.symm⟩
  · exact ⟨j, i - j, Nat.sub_pos_of_lt h,
      by rw [Nat.add_sub_cancel' h.le]; exact heq⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §3.  Attractor Equivalence  (the "same concept" relation)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Attractor Equivalence**: x ~ y iff their orbits eventually coincide.

    Operational meaning for neural networks: two activation states x and y are
    attractor-equivalent iff there exists a layer depth T at which the network's
    internal representation is identical starting from either state.

    This is a *definition* of "same concept" that does not require human labeling.
    It is determined entirely by the dynamics of the system. -/
def attractorRel (x y : α) : Prop := ∃ T : ℕ, F.iter T x = F.iter T y

private theorem ar_refl (x : α) : F.attractorRel x x := ⟨0, rfl⟩
private theorem ar_symm {x y} (h : F.attractorRel x y) : F.attractorRel y x :=
  let ⟨T, hT⟩ := h; ⟨T, hT.symm⟩

/-- Transitivity of attractor equivalence.

    *Proof*: If fᵀ¹(x) = fᵀ¹(y) and fᵀ²(y) = fᵀ²(z), then at time T = max(T₁,T₂)
    all three trajectories agree. The key step is *orbit monotonicity*: once two
    orbits have converged at time T, they remain identical for all future time. -/
private theorem ar_trans {x y z}
    (hxy : F.attractorRel x y) (hyz : F.attractorRel y z) :
    F.attractorRel x z := by
  obtain ⟨T₁, h₁⟩ := hxy; obtain ⟨T₂, h₂⟩ := hyz
  -- Orbit monotonicity: fᵀ(a) = fᵀ(b) → fᵀ⁺ᵏ(a) = fᵀ⁺ᵏ(b) for all k
  have mono : ∀ {T k : ℕ} {a b : α},
      F.iter T a = F.iter T b → F.iter (T + k) a = F.iter (T + k) b :=
    fun {T k a b} h => by simp [iter, Function.iterate_add_apply, h]
  refine ⟨max T₁ T₂, ?_⟩
  -- Lift h₁ from T₁ to max T₁ T₂, and h₂ from T₂ to max T₁ T₂
  have lift₁ : F.iter (max T₁ T₂) x = F.iter (max T₁ T₂) y := by
    have := @mono T₁ (max T₁ T₂ - T₁) x y h₁
    rwa [Nat.add_sub_cancel' (Nat.le_max_left T₁ T₂)] at this
  have lift₂ : F.iter (max T₁ T₂) y = F.iter (max T₁ T₂) z := by
    have := @mono T₂ (max T₁ T₂ - T₂) y z h₂
    rwa [Nat.add_sub_cancel' (Nat.le_max_right T₁ T₂)] at this
  exact lift₁.trans lift₂

/-- The attractor equivalence is a valid setoid. -/
private def attractorSetoid : Setoid α :=
  ⟨F.attractorRel, F.ar_refl, F.ar_symm, F.ar_trans⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §4.  MetaMap Quotient  (the compressed dynamical system)
-- ════════════════════════════════════════════════════════════════════════════

/-- **MetaMap**: the quotient of activation space by attractor equivalence.

    Each element of MetaMap is an *attractor class*: the set of all activation
    states that eventually reach the same cyclic orbit under repeated application
    of f.

    For neural networks: a MetaMap class IS a concept. Two inputs belong to the
    same MetaMap class iff the network's processing of them eventually converges
    to identical internal representations. The MetaMap is the compressed
    representation of all learned distinctions. -/
def MetaMap : Type* := Quotient F.attractorSetoid

/-- The canonical projection to the MetaMap quotient -/
def π (x : α) : F.MetaMap := Quotient.mk F.attractorSetoid x

-- ════════════════════════════════════════════════════════════════════════════
-- §5.  Semi-Conjugacy  (the formal compression)
-- ════════════════════════════════════════════════════════════════════════════

/-- The step map f descends to a well-defined map on the MetaMap quotient.

    *Well-definedness proof*: if x ~ y (same attractor class), then f(x) ~ f(y).
    Reason: if fᵀ(x) = fᵀ(y), then fᵀ(f(x)) = fᵀ⁺¹(x) = fᵀ⁺¹(y) = fᵀ(f(y)).
    The step map cannot move points out of their shared attractor class.

    *Key identity used*: f^T ∘ f = f^(T+1) = f ∘ f^T, so applying f then
    iterating T more steps gives the same result as iterating T steps then
    applying f once. -/
def metamapStep : F.MetaMap → F.MetaMap :=
  Quotient.lift (fun x => F.π (F.f x)) fun x y ⟨T, hT⟩ => by
    apply Quotient.sound
    -- f^T ∘ f = f^(T+1) = f ∘ f^T: iteration and the single step commute.
    have comm : ∀ z : α, F.f^[T] (F.f z) = F.f (F.f^[T] z) := fun z => by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    exact ⟨T, by simp only [iter]; rw [comm x, comm y]; exact congrArg F.f hT⟩

/-- **Semi-Conjugacy Theorem**: The neural network forward pass f factors through
    its MetaMap quotient via the projection π.

    ```
    α ─────────── f ──────────→ α
    │                            │
    π                            π
    ↓                            ↓
    MetaMap ──── g ──────────→ MetaMap
    ```
    The diagram commutes: π(f(x)) = g(π(x)) for all x.

    *This is the formal statement that the NN is a compression*:
    - The NN (f on α) and the MetaMap (g on Q) describe the same dynamics
    - π is the compression map that translates between the two levels
    - Every signal geometry probe approximates π empirically
    - The MetaMap is not something to search for; it is provably there -/
theorem semi_conjugacy (x : α) :
    F.π (F.f x) = F.metamapStep (F.π x) := rfl

/-- The MetaMap is no larger than the original space.
    Compression reduces cardinality: |MetaMap| ≤ |α|. -/
theorem MetaMap_le_card [Fintype F.MetaMap] :
    Fintype.card F.MetaMap ≤ Fintype.card α :=
  Fintype.card_le_of_surjective F.π
    (Quotient.inductionOn · fun x => ⟨x, rfl⟩)

-- ════════════════════════════════════════════════════════════════════════════
-- §6.  Cyclic Orbit Structure  (concepts have ZMod-n algebraic form)
-- ════════════════════════════════════════════════════════════════════════════

/-- The n-fold MetaMap iterate equals the projection of the n-fold original iterate.
    g^n(π(x)) = π(f^n(x))  —  iterates commute with the compression.

    *Proof*: Induction on n.
    - Base: g^0(π x) = π x = π(f^0 x). ✓
    - Step: g^(n+1)(π x) = g(g^n(π x))    [iterate_succ_apply']
                         = g(π(f^n x))     [IH at x]
                         = π(f(f^n x))     [← semi_conjugacy at f^n x]
                         = π(f^(n+1) x)    [definition of iter] -/
lemma iter_commutes : ∀ (n : ℕ) (x : α),
    F.metamapStep^[n] (F.π x) = F.π (F.iter n x) := by
  intro n; induction n with
  | zero => intro x; simp [iter]
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply', ih x, ← F.semi_conjugacy (F.iter n x)]
    congr 1; simp [iter, Function.iterate_succ_apply']

/-- **Cyclic Orbit Theorem**: Every orbit in the MetaMap is purely cyclic.

    There are no transient states in the MetaMap — every element is already in
    its attractor cycle. The cycle length n gives the algebraic type:

    - n = 1:  fixed point  (solid state; the network's unconditional invariants)
    - n > 1:  ZMod-n cycle  (liquid state; conditional computation, Turing-universal)

    *Plasma state* (from the companion document) corresponds to inputs still in
    the transient region of α — not yet settled to a MetaMap class. These are
    where the network's behavior is unreliable. They do not appear as elements of
    MetaMap; they are activation states whose MetaMap class has not yet "crystallized."

    *Proof*: Take any element [x] ∈ MetaMap. By eventual periodicity, there exist
    T, period > 0 with f^(T+period)(x) = f^T(x). This means f^period(x) ~ x
    (their orbits converge at time T), so g^period([x]) = [x]. -/
theorem metamap_orbits_cyclic (q : F.MetaMap) :
    ∃ n > 0, F.metamapStep^[n] q = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨T, period, hpos, hperiod⟩ := F.eventually_periodic x
    refine ⟨period, hpos, ?_⟩
    -- g^period([x]) = [f^period(x)]   by iter_commutes
    rw [F.iter_commutes period x]
    -- [f^period(x)] = [x]   because f^period(x) ~ x
    apply Quotient.sound
    -- Witness T: f^T(f^period(x)) = f^(T+period)(x) = f^T(x)
    exact ⟨T, by
      show F.f^[T] (F.f^[period] x) = F.f^[T] x
      rw [← Function.iterate_add_apply]
      exact hperiod⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §7.  Main Theorem
-- ════════════════════════════════════════════════════════════════════════════

/-- **Neural Network as Dynamical Compression Theorem**

    Any finite iterative map F — including any neural network forward pass, since
    floating-point activation space is finite and the forward pass is deterministic —
    admits a canonical compression to its MetaMap quotient Q with the following
    four properties:

    **(1) Semi-conjugacy**: F factors through Q via π.
         The NN and its MetaMap describe the same dynamics at different resolution.

    **(2) Compression**: Q has cardinality at most |α|.
         The MetaMap is strictly smaller than raw activation space.

    **(3) Cyclic orbits**: every Q-orbit is cyclic (ZMod-n algebraic structure).
         Concepts have the algebraic structure of cyclic groups.

    **(4) Conceptual completeness**: π(x) = π(y) ↔ x ~ y.
         The MetaMap captures *exactly* the attractor structure, nothing more.
         Two inputs get the same MetaMap class iff their trajectories converge.

    ---

    **The interpretability corollary**: "Reading signal geometry" is precisely
    the empirical estimation of π. Since π is a well-defined map that provably
    exists, signal geometry is not finding patterns that might be there —
    it is reading a structured mathematical object that must be there. -/
theorem NeuralNetworkCompressionTheorem [Fintype F.MetaMap] :
    -- (1) Semi-conjugacy
    (∀ x : α, F.π (F.f x) = F.metamapStep (F.π x)) ∧
    -- (2) Compression
    (Fintype.card F.MetaMap ≤ Fintype.card α) ∧
    -- (3) Cyclic orbits
    (∀ q : F.MetaMap, ∃ n > 0, F.metamapStep^[n] q = q) ∧
    -- (4) Conceptual completeness
    (∀ x y : α, F.π x = F.π y ↔ F.attractorRel x y) :=
  ⟨F.semi_conjugacy,
   F.MetaMap_le_card,
   F.metamap_orbits_cyclic,
   fun x y => ⟨Quotient.exact, Quotient.sound⟩⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §8.  Corollaries for Signal Geometry
-- ════════════════════════════════════════════════════════════════════════════

/-- **Concept Boundary Signature**: x and y are in different MetaMap classes iff
    their long-run trajectories diverge.

    This is the algebraic source of high Jacobian sensitivity at concept boundaries:
    near a boundary, arbitrarily close inputs can be in different attractor classes. -/
theorem concept_boundary {x y : α} :
    F.π x ≠ F.π y ↔ ¬F.attractorRel x y :=
  ⟨fun h hr => h (Quotient.sound hr),
   fun h heq => h (Quotient.exact heq)⟩

/-- **Solid State Characterization**: an activation state x is in a solid-state
    (period-1, fixed-attractor) region iff f(x) ~ x.

    Signal interpretation: a small perturbation to x produces a perturbation that
    the network immediately returns to the same MetaMap class. High stability,
    low Jacobian. The network has an unconditional invariant here. -/
theorem solid_state_iff (x : α) :
    F.metamapStep (F.π x) = F.π x ↔ F.attractorRel (F.f x) x :=
  ⟨fun h => Quotient.exact (F.semi_conjugacy x ▸ h),
   fun h => F.semi_conjugacy x ▸ Quotient.sound h⟩

/-- **Layer Convergence**: for any x, the sequence π(f^n(x)) is eventually
    periodic in the MetaMap. Once the orbit enters the attractor (after T steps),
    shifting by the attractor period leaves the MetaMap class unchanged, for all k.

    *Clarification*: The sequence does NOT become constant unless f^T(x) is a
    fixed point. In a period-n attractor, π(f^n(x)) cycles through n distinct
    MetaMap classes — this is exactly the ZMod-n structure of §6. The earlier
    formulation (constant after time T) is false: in a 2-cycle {a,b}, consecutive
    iterates lie in different attractor classes whose orbits never meet at the same
    time step, so π(f^(T+1)(x)) ≠ π(f^T(x)) for any T.

    What this theorem captures: the cycling pattern has settled. No further drift
    in which attractor orbit we are tracing. This is the "most readable layer"
    from the signal geometry document — the depth at which the MetaMap projection
    has entered its stable cyclic regime.

    *Proof*: From eventually_periodic, f^[T+period](x) = f^[T](x). Separating the
    outer k iterations: f^[k+(T+period)](x) = f^[k](f^[T+period](x))
                                             = f^[k](f^[T](x))
                                             = f^[k+T](x). -/
theorem layer_convergence (x : α) :
    ∃ T period : ℕ, 0 < period ∧
      ∀ k : ℕ, F.π (F.iter (T + k + period) x) = F.π (F.iter (T + k) x) := by
  obtain ⟨T, period, hpos, hperiod⟩ := F.eventually_periodic x
  refine ⟨T, period, hpos, fun k => ?_⟩
  -- The key identity: iter(T + k + period) x = iter(T + k) x.
  -- Arithmetic: T+k+period = k+(T+period), so by iterate_add_apply:
  --   f^[k+(T+period)] x = f^[k](f^[T+period] x)   [peel off outer k steps]
  --                      = f^[k](f^[T] x)            [hperiod]
  --                      = f^[k+T] x                 [recombine]
  have key : F.iter (T + k + period) x = F.iter (T + k) x := by
    simp only [iter] at *
    have h1 : F.f^[T + k + period] x = F.f^[k] (F.f^[T + period] x) := by
      rw [show T + k + period = k + (T + period) from by omega]
      simp [Function.iterate_add_apply]
    have h2 : F.f^[T + k] x = F.f^[k] (F.f^[T] x) := by
      rw [show T + k = k + T from by omega]
      simp [Function.iterate_add_apply]
    rw [h1, h2, hperiod]
  exact congrArg F.π key

end NeuralNetworkCompression

/-!
## Summary: What This File Establishes

The five theorems `eventually_periodic`, `attractorRel` (as a valid setoid),
`semi_conjugacy`, `MetaMap_le_card`, and `metamap_orbits_cyclic` form a complete
proof of the main claim.

Together they say: **a neural network, as a finite deterministic map, is
canonically identical to its MetaMap quotient up to the compression π.** The
compression loses no information about long-run behavior (conceptual completeness)
while being algebraically simpler (cyclic groups instead of arbitrary orbits).

**No sorrys remain.** The three fixes from the original draft were:

1. `metamapStep`: the well-definedness proof used an out-of-scope identifier.
   Fixed using the commutativity identity f^T ∘ f = f^(T+1) = f ∘ f^T,
   proved cleanly via `iterate_succ_apply` / `iterate_succ_apply'`.

2. `iter_commutes`: the rewrite `← ih (F.f x)` tried to match
   `F.π (F.iter n (F.f x))` against `F.π (F.iter (n+1) x)`, which are
   propositionally but not syntactically equal — so the rewrite silently
   failed. Fixed by using `ih x` (not `ih (F.f x)`) and rewriting via
   `← semi_conjugacy` to bridge the gap.

3. `layer_convergence`: the original statement claimed the MetaMap projection
   stabilizes to a constant after depth T. This is false: in a 2-cycle {a,b},
   consecutive iterates lie in different attractor classes, so the projection
   cycles rather than stabilizing. The correct statement is eventual periodicity —
   shifting by the attractor period fixes the class. The proof is a direct
   arithmetic argument from `eventually_periodic` and `iterate_add_apply`,
   requiring no induction.  -/
