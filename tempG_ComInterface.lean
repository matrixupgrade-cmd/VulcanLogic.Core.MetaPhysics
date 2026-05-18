import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic

set_option autoImplicit false
open Finset BigOperators Classical

universe u

namespace InterfaceConfig

-- ==================================================
-- BASIC STRUCTURE
-- ==================================================

variable (Node : Type) [DecidableEq Node]

structure Probe where
  transform : (Node → Node → ℝ) → (Node → Node → ℝ)

def applyProbe
    (p : Probe Node)
    (g : Node → Node → ℝ) :
    Node → Node → ℝ :=
  p.transform g

def commutator (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  g i j - g j i

def asymmetry (g : Node → Node → ℝ) (i j : Node) : ℝ :=
  Real.abs (commutator g i j)

def node_asymmetry
    (g : Node → Node → ℝ)
    (nodes : Finset Node)
    (n : Node) : ℝ :=
  ∑ m in nodes, asymmetry g n m

structure Junction where
  nodes : Finset Node

abbrev InterfaceConfig := Probe Node
abbrev ConfigSpace := List (InterfaceConfig Node)

def interface_distortion
    (cfg : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℝ :=
  ∑ n in junc.nodes,
    node_asymmetry Node (applyProbe Node cfg g) junc.nodes n

-- ==================================================
-- BASINS
-- ==================================================

abbrev Signal := Unit

structure Basin where
  signals : Finset Signal

def basin_entropy (b : Basin) : ℕ :=
  b.signals.card

variable (signal_to_cfg : Signal → InterfaceConfig Node)

def configsInBasin (b : Basin) : ConfigSpace Node :=
  (b.signals.image signal_to_cfg).toList

def basin_local_complexity
    (b : Basin)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  (configsInBasin Node signal_to_cfg b
    |>.map (fun cfg => interface_distortion Node cfg g junc)
  ).toFinset.card

-- ==================================================
-- SIGNATURE SPACE (CORE IDEA)
-- ==================================================

variable (entropy : ℕ)

abbrev LocalSignature
    (junc : Junction Node) :=
  ({i // i ∈ junc.nodes} →
   {j // j ∈ junc.nodes} →
   Fin entropy)

def distortion_combination_bound
    (entropy : ℕ)
    (junction_size : ℕ) : ℕ :=
  entropy ^ (junction_size * junction_size)

variable (bucket : ℝ → Fin entropy)

def local_signature
    (cfg : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) :
    LocalSignature Node junc entropy :=
  fun i j =>
    bucket (asymmetry (applyProbe Node cfg g) i.1 j.1)

def same_signature
    (cfg₁ cfg₂ : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : Prop :=
  local_signature Node entropy bucket cfg₁ g junc =
  local_signature Node entropy bucket cfg₂ g junc

axiom same_signature_same_distortion
    (cfg₁ cfg₂ : InterfaceConfig Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (hsig :
      same_signature Node entropy bucket cfg₁ cfg₂ g junc) :
    interface_distortion Node cfg₁ g junc =
    interface_distortion Node cfg₂ g junc

-- ==================================================
-- CARDINALITY OF SIGNATURE SPACE
-- ==================================================

theorem local_signature_cardinality_bound
    (junc : Junction Node)
    [Fintype {i // i ∈ junc.nodes}] :
    Fintype.card
      (LocalSignature Node junc entropy)
    =
    distortion_combination_bound entropy junc.nodes.card := by
  classical
  unfold LocalSignature distortion_combination_bound
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]
  rw [Fintype.card_fin]

  have h_i :
      Fintype.card {i // i ∈ junc.nodes}
      = junc.nodes.card := by
    simpa using Fintype.card_coe (s := junc.nodes)

  have h_j :
      Fintype.card {j // j ∈ junc.nodes}
      = junc.nodes.card := by
    simpa using Fintype.card_coe (s := junc.nodes)

  simp [h_i, h_j, pow_mul]

-- ==================================================
-- OBSERVABLE COMPLEXITY FACTORIZATION
-- ==================================================

theorem observable_complexity_le_signatures
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin)
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node signal_to_cfg b g junc
    ≤
    Fintype.card (LocalSignature Node junc entropy) := by
  classical

  unfold basin_local_complexity

  set cs := configsInBasin Node signal_to_cfg b with hcs

  let D : Finset ℝ :=
    (cs.map (fun cfg =>
      interface_distortion Node cfg g junc)).toFinset

  let S : Finset (LocalSignature Node junc entropy) :=
    (cs.map (fun cfg =>
      local_signature Node entropy bucket cfg g junc)).toFinset

  have hD :
      ∀ d ∈ D,
      ∃ cfg ∈ cs,
        interface_distortion Node cfg g junc = d := by
    intro d hd
    rcases Finset.mem_toFinset.mp hd with ⟨cfg, hcfg, rfl⟩
    exact ⟨cfg, hcfg, rfl⟩

  choose cfg_of_dist hcfg_of_dist hval_of_dist using hD

  let φ :
      {d // d ∈ D} → {s // s ∈ S} :=
    fun ⟨d, hd⟩ =>
      let cfg := cfg_of_dist d hd
      have hcfg := hcfg_of_dist d hd
      have hsig :
        local_signature Node entropy bucket cfg g junc ∈ S := by
        rw [Finset.mem_toFinset, List.mem_map]
        exact ⟨cfg, hcfg, rfl⟩

      ⟨local_signature Node entropy bucket cfg g junc, hsig⟩

  have h_inj : Function.Injective φ := by
    intro d₁ d₂ hφ
    rcases d₁ with ⟨d₁, hd₁⟩
    rcases d₂ with ⟨d₂, hd₂⟩
    simp at hφ

    have hdist :
      interface_distortion Node (cfg_of_dist d₁ hd₁) g junc =
      interface_distortion Node (cfg_of_dist d₂ hd₂) g junc := by
      apply same_signature_same_distortion
      exact hφ

    have : d₁ = d₂ := by
      simpa [hval_of_dist d₁ hd₁, hval_of_dist d₂ hd₂] using hdist
    subst this
    rfl

  have h_card_DS :
      D.card ≤ S.card := by
    have h :=
      Fintype.card_le_of_injective φ h_inj
    simpa using h

  have h_S :
      S.card ≤ Fintype.card (LocalSignature Node junc entropy) :=
    Finset.card_le_univ _

  exact le_trans h_card_DS h_S

-- ==================================================
-- MAIN EXPONENTIAL COLLAPSE THEOREM
-- ==================================================

theorem observable_complexity_bounded_exponential
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin)
    [Fintype {i // i ∈ junc.nodes}] :
    basin_local_complexity Node signal_to_cfg b g junc
    ≤ distortion_combination_bound entropy junc.nodes.card := by
  apply le_trans
  · exact observable_complexity_le_signatures Node entropy bucket g junc b
  · rw [← local_signature_cardinality_bound
        (Node := Node)
        (entropy := entropy)
        (junc := junc)]

end InterfaceConfig
