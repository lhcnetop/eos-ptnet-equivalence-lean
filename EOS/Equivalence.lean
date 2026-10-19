/-
Copyright (c) 2025 Luis Henrique Costa Neto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luis Henrique Costa Neto
-/

module

public import EOS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# Equivalence of EOS under reference semantics and P/T nets

**Main theorem.** For every EOS `E` under reference semantics, the relation between an EOS
marking and its equivalent marking in the P/T net `eosEquivNet E` is a bisimulation between
the labelled transition systems they generate, with identical labels on both sides.

## Main statements

- `eosEquivNet_enabled_iff`: an action is enabled in the EOS iff the corresponding
  transition is enabled in the equivalent net.
- `eosEquivNet_fire_eq`: firing commutes with the translation of markings.
- `eos_bisimulation`: the main theorem.
- `eosToPTMarking_injective`: the translation of markings is injective.
-/

@[expose] public section

namespace Dissertation

open Cslib.PetriNet

variable {k : ℕ} (E : EOS k)

/-- An EOS marking and a marking of the equivalent P/T net are related iff the latter is
the translation of the former. -/
def eosStateRel (m : EOSMarking E) (m' : Marking (EOSPlaces E)) : Prop :=
  m' = eosToPTMarking E m

/-- Firing an action in the equivalent net corresponds to firing it in the EOS, place by
place. -/
theorem eosEquivNet_fire_eq (m : EOSMarking E) (a : EOSAction k E.T_sys E.T_obj)
    (ha : a.Valid E) :
    (eosEquivNet E).fire (eosToPTMarking E m) ⟨a, ha⟩ = eosToPTMarking E (a.fire E m) := by
  funext p
  obtain ⟨p, i⟩ | p | ⟨i, p⟩ := p
  · simp only [PTNet.fire, eosEquivNet, eosToPTMarking, EOSAction.fire]
    by_cases hij : i = a.netIdx
    · subst hij
      cases a.tSys <;> simp [TauOr.weight]
    · simp [hij]
  · simp only [PTNet.fire, eosEquivNet, eosToPTMarking, EOSAction.fire]
    cases a.tSys <;> simp [TauOr.weight]
  · simp only [PTNet.fire, eosEquivNet, eosToPTMarking, EOSAction.fire]
    by_cases hij : i = a.netIdx
    · subst hij
      rw [Function.update_self]
      cases a.tObj <;> simp [TauOr.weight]
    · rw [Function.update_of_ne hij]
      simp [hij]

/-- An action is enabled in the EOS iff it is enabled, as a transition, in the equivalent
P/T net. -/
theorem eosEquivNet_enabled_iff (m : EOSMarking E) (a : EOSAction k E.T_sys E.T_obj)
    (ha : a.Valid E) :
    (eosEquivNet E).Enabled (eosToPTMarking E m) ⟨a, ha⟩ ↔ a.Enabled E m := by
  simp only [PTNet.Enabled, EOSAction.Enabled, SysEnabled, ObjEnabled]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · cases ha' : a.tObj with
      | tau => trivial
      | some t =>
        intro p
        have := h (Sum.inr (Sum.inr ⟨a.netIdx, p⟩))
        simpa [eosEquivNet, eosToPTMarking, ha'] using this
    · cases ha' : a.tSys with
      | tau => trivial
      | some tHat =>
        refine ⟨fun p => ?_, fun p => ?_⟩
        · have := h (Sum.inl (p, a.netIdx))
          simpa [eosEquivNet, eosToPTMarking, ha'] using this
        · have := h (Sum.inr (Sum.inl p))
          simpa [eosEquivNet, eosToPTMarking, ha'] using this
  · rintro ⟨hobj, hsys⟩ p
    obtain ⟨p, i⟩ | p | ⟨i, p⟩ := p
    · by_cases hij : i = a.netIdx
      · subst hij
        simp only [eosEquivNet, eosToPTMarking]
        revert hsys
        cases a.tSys with
        | tau => intro _; simp
        | some tHat => intro hsys; exact hsys.1 p
      · simp [hij, eosEquivNet, eosToPTMarking]
    · simp only [eosEquivNet, eosToPTMarking]
      revert hsys
      cases a.tSys with
      | tau => intro _; simp
      | some tHat => intro hsys; exact hsys.2 p
    · by_cases hij : i = a.netIdx
      · subst hij
        simp only [eosEquivNet, eosToPTMarking]
        revert hobj
        cases a.tObj with
        | tau => intro _; simp
        | some t => intro hobj; exact hobj p
      · simp [hij, eosEquivNet, eosToPTMarking]

/-- **Main theorem.** The relation `eosStateRel E` is a bisimulation between the LTS of the
EOS and the LTS of its equivalent P/T net. -/
theorem eos_bisimulation :
    Cslib.LTS.IsBisimulation (eosToLTS E) (PTNet.toLTS (eosEquivNet E)) (eosStateRel E) := by
  intro m m' hrel a
  obtain ⟨a, ha⟩ := a
  subst hrel
  constructor
  · rintro n ⟨hen, hfire⟩
    refine ⟨eosToPTMarking E n, ⟨?_, ?_⟩, rfl⟩
    · exact (eosEquivNet_enabled_iff E m a ha).mpr hen
    · rw [eosEquivNet_fire_eq E m a ha, hfire]
  · rintro n' ⟨hen', hfire'⟩
    refine ⟨a.fire E m, ⟨(eosEquivNet_enabled_iff E m a ha).mp hen', rfl⟩, ?_⟩
    change n' = eosToPTMarking E (a.fire E m)
    rw [← hfire', eosEquivNet_fire_eq E m a ha]

/-- The translation of markings is injective. -/
theorem eosToPTMarking_injective (m₁ m₂ : EOSMarking E) :
    eosToPTMarking E m₁ = eosToPTMarking E m₂ → m₁ = m₂ := by
  intro h
  obtain ⟨⟨ob₁, bt₁⟩, obj₁⟩ := m₁
  obtain ⟨⟨ob₂, bt₂⟩, obj₂⟩ := m₂
  have hob : ob₁ = ob₂ := funext fun p => funext fun i => congrFun h (Sum.inl (p, i))
  have hbt : bt₁ = bt₂ := funext fun p => congrFun h (Sum.inr (Sum.inl p))
  have hobjf : obj₁ = obj₂ := funext fun i => funext fun p => congrFun h (Sum.inr (Sum.inr ⟨i, p⟩))
  subst hob; subst hbt; subst hobjf; rfl

end Dissertation
