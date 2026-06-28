import Mathlib

open Classical

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-!
# Basin symmetry conflict

Setting: a finite type `State` with a self-map `step : State → State`.

A *basin* is a nonempty, closed, strongly-connected orbit of `step` — a
single finite cycle. A binary operation `couple : State → State → State`
combines an element of one basin with an element of another; no algebraic
structure is assumed on `couple`.

Main result: if coupling an element of one basin with an element of a
second, disjoint basin produces a state outside both basins, and every
iterate of that state under `step` remains outside both basins, then the
forward orbit of that state is itself a basin, disjoint from the first two.
-/

/-!
## Basins
-/

/-- A nonempty finite set of states, closed under `step`, on which `step`
acts transitively: every element reaches every other element by some number
of iterations. Equivalently, a single cycle of `step`. -/
structure Basin (step : State → State) where
  carrier   : Finset State
  nonempty  : carrier.Nonempty
  closed    : ∀ x ∈ carrier, step x ∈ carrier
  connected : ∀ x ∈ carrier, ∀ y ∈ carrier, ∃ n : ℕ, step^[n] x = y

/-!
## Coupling and boundary conflict
-/

/-- `x` is `couple a b` for some `a ∈ B1` and `b ∈ B2`, and `x` belongs to
neither basin. -/
def IsBoundaryProduct {step : State → State} (couple : State → State → State)
    (B1 B2 : Basin step) (x : State) : Prop :=
  ∃ a ∈ B1.carrier, ∃ b ∈ B2.carrier, couple a b = x ∧ x ∉ B1.carrier ∪ B2.carrier

/-- Every iterate of `x` belongs to neither `B1` nor `B2`. -/
def Persists {step : State → State} (B1 B2 : Basin step) (x : State) : Prop :=
  ∀ n : ℕ, step^[n] x ∉ B1.carrier ∪ B2.carrier

/-- `x` is a boundary product whose exclusion from both basins persists
under iteration. -/
def PersistentConflict {step : State → State} (couple : State → State → State)
    (B1 B2 : Basin step) (x : State) : Prop :=
  IsBoundaryProduct couple B1 B2 x ∧ Persists B1 B2 x

/-!
## Periodicity

`State` is finite, so every orbit of `step` is eventually periodic. The two
lemmas below give exactly what the main theorem needs: existence of a
periodic point on any orbit, and the fact that once a point is periodic, all
of its iterates are determined by index modulo the period.
-/

/-- If `step^[p] y = y` for some `p > 0`, then `step^[a] y` depends only on
`a % p`. -/
private lemma iterate_mod {step : State → State} {y : State} {p : ℕ}
    (hp : 0 < p) (hper : step^[p] y = y) :
    ∀ a : ℕ, step^[a] y = step^[a % p] y := by
  have key : ∀ m a : ℕ, step^[p * m + a] y = step^[a] y := by
    intro m
    induction m with
    | zero => intro a; simp
    | succ m ih =>
        intro a
        have hrw : p * (m + 1) + a = (p * m + a) + p := by ring
        rw [hrw, Function.iterate_add_apply, hper, ih]
  intro a
  have ha : p * (a / p) + a % p = a := Nat.div_add_mod a p
  calc step^[a] y = step^[p * (a / p) + a % p] y := by rw [ha]
    _ = step^[a % p] y := key (a / p) (a % p)

/-- For any `x`, some iterate `step^[k] x` is a periodic point: there is a
`p > 0` with `step^[p] (step^[k] x) = step^[k] x`. Follows from
`step^[·] x : ℕ → State` failing to be injective. -/
private lemma exists_periodic_point (step : State → State) (x : State) :
    ∃ k p : ℕ, 0 < p ∧ step^[p] (step^[k] x) = step^[k] x := by
  obtain ⟨i, j, hij, hfij⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => step^[n] x)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨i, j - i, by omega, ?_⟩
    calc step^[j - i] (step^[i] x)
        = step^[(j - i) + i] x := (Function.iterate_add_apply step (j - i) i x).symm
      _ = step^[j] x := by
            have h : (j - i) + i = j := by omega
            rw [h]
      _ = step^[i] x := hfij.symm
  · refine ⟨j, i - j, by omega, ?_⟩
    calc step^[i - j] (step^[j] x)
        = step^[(i - j) + j] x := (Function.iterate_add_apply step (i - j) j x).symm
      _ = step^[i] x := by
            have h : (i - j) + j = i := by omega
            rw [h]
      _ = step^[j] x := hfij

/-!
## Main theorem
-/

/-- A persistent boundary conflict between two basins produces a third
basin, disjoint from both.

Proof: some iterate `y = step^[k] x` is periodic with period `p > 0`
(`exists_periodic_point`). The image of `{0, ..., p - 1}` under
`fun m => step^[m] y` is nonempty, closed under `step`, and
strongly-connected — all by `iterate_mod` — hence a basin. Every element of
this set equals `step^[n] x` for some `n`, so `Persists` excludes it from
`B1 ∪ B2`. -/
theorem persistent_conflict_generates_new_basin
    {step : State → State} {couple : State → State → State}
    {B1 B2 : Basin step} {x : State}
    (hdisjoint : Disjoint B1.carrier B2.carrier)
    (hconflict : PersistentConflict couple B1 B2 x) :
    ∃ B3 : Basin step, Disjoint B3.carrier (B1.carrier ∪ B2.carrier) := by
  -- hdisjoint is not needed by the construction below; only the persistence
  -- half of hconflict is used.
  obtain ⟨_, hpersist⟩ := hconflict
  obtain ⟨k, p, hp, hper⟩ := exists_periodic_point step x
  set y := step^[k] x with hy
  have hmod : ∀ a : ℕ, step^[a] y = step^[a % p] y := iterate_mod hp hper
  refine ⟨⟨(Finset.range p).image (fun m => step^[m] y), ?_, ?_, ?_⟩, ?_⟩
  · -- nonempty: y itself is in the image
    exact ⟨y, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩⟩
  · -- closed under step
    intro z hz
    obtain ⟨m, hm, hmz⟩ := Finset.mem_image.mp hz
    have hstep : step z = step^[m + 1] y := by
      rw [← hmz, Function.iterate_succ_apply']
    have hmodstep : step^[m + 1] y = step^[(m + 1) % p] y := hmod (m + 1)
    refine Finset.mem_image.mpr ⟨(m + 1) % p, Finset.mem_range.mpr (Nat.mod_lt (m + 1) hp), ?_⟩
    rw [← hmodstep, ← hstep]
  · -- strongly connected
    intro z1 hz1 z2 hz2
    obtain ⟨k1, hk1, hz1eq⟩ := Finset.mem_image.mp hz1
    obtain ⟨k2, hk2, hz2eq⟩ := Finset.mem_image.mp hz2
    have hk1p : k1 < p := Finset.mem_range.mp hk1
    have hk2p : k2 < p := Finset.mem_range.mp hk2
    refine ⟨k2 + (p - k1), ?_⟩
    have hn : (k2 + (p - k1)) + k1 = k2 + p := by omega
    calc step^[k2 + (p - k1)] z1
        = step^[k2 + (p - k1)] (step^[k1] y) := by rw [hz1eq]
      _ = step^[(k2 + (p - k1)) + k1] y :=
            (Function.iterate_add_apply step (k2 + (p - k1)) k1 y).symm
      _ = step^[k2 + p] y := by rw [hn]
      _ = step^[k2] y := by
            have h := hmod (k2 + p)
            have heq : (k2 + p) % p = k2 := by
              rw [Nat.add_mod_right]
              exact Nat.mod_eq_of_lt hk2p
            rw [heq] at h
            exact h
      _ = z2 := hz2eq
  · -- disjoint from B1 ∪ B2
    rw [Finset.disjoint_left]
    intro z hz
    obtain ⟨m, _, hmz⟩ := Finset.mem_image.mp hz
    have heq2 : step^[m] y = step^[m + k] x := by
      rw [hy]
      exact (Function.iterate_add_apply step m k x).symm
    rw [← hmz, heq2]
    exact hpersist (m + k)
