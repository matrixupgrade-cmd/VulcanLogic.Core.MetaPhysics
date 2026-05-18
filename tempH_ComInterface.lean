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

def applyProbe (p : Probe Node) (g : Node → Node → ℝ) :=
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
-- OBSERVABLE COMPLEXITY
-- ==================================================

def observable_complexity
    (cs : ConfigSpace Node)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  (cs.map (fun cfg => interface_distortion Node cfg g junc)).toFinset.card

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

lemma configsInBasin_length_le_entropy (b : Basin) :
    (configsInBasin Node signal_to_cfg b).length ≤ basin_entropy b := by
  unfold configsInBasin basin_entropy
  simpa using Finset.card_image_le (f := signal_to_cfg)

def basin_local_complexity
    (b : Basin)
    (g : Node → Node → ℝ)
    (junc : Junction Node) : ℕ :=
  observable_complexity Node (configsInBasin Node signal_to_cfg b) g junc

-- ==================================================
-- LOCAL SIGNATURE SPACE
-- ==================================================

variable (entropy : ℕ)

abbrev LocalSignature (junc : Junction Node) :=
  ({i // i ∈ junc.nodes} →
   {j // j ∈ junc.nodes} →
   Fin entropy)

theorem local_signature_cardinality_bound
    (junc : Junction Node)
    [Fintype {i // i ∈ junc.nodes}] :
    Fintype.card (LocalSignature Node entropy junc)
      =
    entropy ^ (junc.nodes.card * junc.nodes.card) := by
  classical
  unfold LocalSignature
  simp [Fintype.card_fun, Fintype.card_fin, pow_mul]
  have h :
      Fintype.card {i // i ∈ junc.nodes} = junc.nodes.card :=
    Fintype.card_coe junc.nodes
  simpa [h, pow_mul]

-- ==================================================
-- SIGNATURE MODEL
-- ==================================================

variable (local_signature :
  InterfaceConfig Node → LocalSignature Node entropy junc)

variable (h_signature_determines_distortion :
  ∀ cfg₁ cfg₂,
    local_signature cfg₁ = local_signature cfg₂ →
    interface_distortion Node cfg₁ g junc =
    interface_distortion Node cfg₂ g junc)

-- ==================================================
-- COMPLEXITY FACTORING STEP (NOW COMPLETE)
-- ==================================================

theorem observable_complexity_le_signatures
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin) :
    basin_local_complexity Node signal_to_cfg b g junc ≤
      Fintype.card (LocalSignature Node entropy junc) := by
  classical
  unfold basin_local_complexity observable_complexity
  set cs := configsInBasin Node signal_to_cfg b with hcs

  let D :=
    (cs.map (fun cfg =>
      interface_distortion Node cfg g junc)).toFinset

  let S :=
    (cs.map (fun cfg =>
      local_signature cfg)).toFinset

  have hD_le_S :
      D.card ≤ S.card := by
    classical
    -- witness distortion comes from a config
    have hD_witness :
        ∀ d ∈ D,
        ∃ cfg ∈ cs,
          interface_distortion Node cfg g junc = d := by
      intro d hd
      rcases Finset.mem_toFinset.mp hd with ⟨cfg, hcfg, rfl⟩
      exact ⟨cfg, hcfg, rfl⟩

    choose cfg_of_dist hcfg_of_dist hval_of_dist using hD_witness

    let φ :
        {d // d ∈ D} →
        {s // s ∈ S} :=
      fun ⟨d, hd⟩ =>
        let cfg := cfg_of_dist d hd
        have hcfg : cfg ∈ cs := hcfg_of_dist d hd
        have hsig : local_signature cfg ∈ S := by
          refine Finset.mem_toFinset.mpr ?_
          exact ⟨cfg, hcfg, rfl⟩
        ⟨local_signature cfg, hsig⟩

    have h_inj : Function.Injective φ := by
      intro d₁ d₂ hφ
      rcases d₁ with ⟨d₁, hd₁⟩
      rcases d₂ with ⟨d₂, hd₂⟩
      simp at hφ

      have hdist :
          interface_distortion Node (cfg_of_dist d₁ hd₁) g junc =
          interface_distortion Node (cfg_of_dist d₂ hd₂) g junc :=
        h_signature_determines_distortion
          (cfg_of_dist d₁ hd₁)
          (cfg_of_dist d₂ hd₂)
          hφ

      have : d₁ = d₂ := by
        simpa [hval_of_dist d₁ hd₁, hval_of_dist d₂ hd₂] using hdist
      subst this
      rfl

    have h' :
        Fintype.card {d // d ∈ D} ≤
        Fintype.card {s // s ∈ S} :=
      Fintype.card_le_of_injective φ h_inj

    have hDcard : Fintype.card {d // d ∈ D} = D.card :=
      Fintype.card_coe D
    have hScard : Fintype.card {s // s ∈ S} = S.card :=
      Fintype.card_coe S

    simpa [hDcard, hScard] using h'

-- ==================================================
-- FINAL EXPONENTIAL BOUND
-- ==================================================

theorem observable_complexity_bounded_exponential
    (g : Node → Node → ℝ)
    (junc : Junction Node)
    (b : Basin) :
    basin_local_complexity Node signal_to_cfg b g junc ≤
      entropy ^ (junc.nodes.card * junc.nodes.card) := by
  have h :=
    observable_complexity_le_signatures
      Node entropy signal_to_cfg local_signature
      h_signature_determines_distortion
      g junc b

  simpa [local_signature_cardinality_bound Node entropy junc] using h

end InterfaceConfig
