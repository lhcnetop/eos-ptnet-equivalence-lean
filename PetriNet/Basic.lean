/-
Copyright (c) 2025 Luis Henrique Costa Neto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luis Henrique Costa Neto
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Basic

/-!
# Place/Transition Nets (P/T Nets)

This file defines Place/Transition Nets (P/T Nets), a classical model of
concurrent and distributed computation introduced by Carl Adam Petri.

## Main definitions

- `Marking P` is the type of markings of a P/T net with places of type `P`,
  representing a distribution of tokens across places as a function `P → ℕ`.
- `PTNet P T` is a P/T net with places of type `P` and transitions of type `T`,
  described by pre- and post-condition weight functions.
- `PTNet.Enabled N M t` states that transition `t` is enabled in marking `M` under net `N`.
- `PTNet.fire N M t` is the marking obtained by firing transition `t` from `M` in `N`.
- `PTNet.Reachable N M₀ M` states that `M` is reachable from `M₀` by a finite sequence of
  enabled firings.

## References

* [W. Reisig, *Petri Nets: An Introduction*][Reisig1985]
* [J.L. Peterson, *Petri Net Theory and the Modeling of Systems*][Peterson1981]
-/

@[expose] public section

namespace Cslib.PetriNet

universe u v

/-- A marking of a P/T net with places of type `P` is a distribution of tokens,
represented as a function assigning a natural number (token count) to each place. -/
abbrev Marking (P : Type u) := P → ℕ

/-- A Place/Transition Net (P/T Net) with places `P` and transitions `T` consists of
pre- and post-condition weight functions specifying how many tokens each transition
consumes from and produces in each place. -/
@[ext]
structure PTNet (P : Type u) (T : Type v) where
  /-- Pre-condition weights: number of tokens consumed from each place per transition. -/
  pre : T → P → ℕ
  /-- Post-condition weights: number of tokens produced in each place per transition. -/
  post : T → P → ℕ

namespace PTNet

variable {P : Type u} {T : Type v} (N : PTNet P T)

/-- Transition `t` is enabled in marking `M` if every place holds at least as many
tokens as required by the pre-condition weight. -/
abbrev Enabled (M : Marking P) (t : T) : Prop :=
  ∀ p, N.pre t p ≤ M p

/-- Firing transition `t` in marking `M` produces a new marking by consuming
`N.pre t p` tokens and producing `N.post t p` tokens at each place `p`.

Note: natural number subtraction is used; enabledness (`Enabled`) ensures `M p ≥ N.pre t p`,
guaranteeing no underflow at enabled transitions. -/
def fire (M : Marking P) (t : T) : Marking P :=
  fun p => M p - N.pre t p + N.post t p

/-! ## Lemmas -/

/-- Unfolds `fire` at a single place. -/
@[simp]
theorem fire_apply (M : Marking P) (t : T) (p : P) :
    N.fire M t p = M p - N.pre t p + N.post t p := rfl

/-- Unfolds `Enabled` as token sufficiency at each place. -/
@[simp]
theorem enabled_iff (M : Marking P) (t : T) :
    N.Enabled M t ↔ ∀ p, N.pre t p ≤ M p := Iff.rfl

/-- When `t` is enabled, the pre-condition is satisfied at every individual place. -/
theorem Enabled.pre_le {M : Marking P} {t : T} (h : N.Enabled M t) (p : P) :
    N.pre t p ≤ M p := h p

/-- Enabledness is monotone: adding tokens to a marking preserves enabledness. -/
theorem Enabled.mono {M M' : Marking P} {t : T}
    (h : N.Enabled M t) (hle : ∀ p, M p ≤ M' p) : N.Enabled M' t :=
  fun p => Nat.le_trans (h p) (hle p)

/-- A transition whose pre-condition is zero everywhere is always enabled. -/
theorem enabled_of_pre_zero {t : T} (h : ∀ p, N.pre t p = 0) (M : Marking P) :
    N.Enabled M t :=
  fun p => by simp [h p]

/-- When `t` is enabled, the number of tokens at `p` after firing satisfies
`(N.fire M t) p + N.pre t p = M p + N.post t p`. -/
theorem fire_token_balance {M : Marking P} {t : T}
    (h : N.Enabled M t) (p : P) :
    N.fire M t p + N.pre t p = M p + N.post t p := by
  simp only [fire_apply]
  have hp := h p
  omega

/-! ## Reachability -/

/-- `N.Reachable M₀ M` holds if marking `M` is reachable from `M₀` by a finite
(possibly empty) sequence of enabled firings in net `N`. -/
inductive Reachable (N : PTNet P T) : Marking P → Marking P → Prop where
  /-- Every marking is reachable from itself (zero firings). -/
  | refl : N.Reachable M M
  /-- If `t` is enabled in `M` and `M'` is reachable from `fire M t`,
  then `M'` is reachable from `M`. -/
  | step {M : Marking P} {t : T} {M' : Marking P}
      (hen : N.Enabled M t)
      (h   : N.Reachable (N.fire M t) M') : N.Reachable M M'

namespace Reachable

variable {N : PTNet P T}

/-- A single enabled firing yields reachability in one step. -/
theorem single {M : Marking P} {t : T} (h : N.Enabled M t) :
    N.Reachable M (N.fire M t) :=
  .step h .refl

/-- Reachability is transitive. -/
theorem trans {M₁ M₂ M₃ : Marking P}
    (h₁ : N.Reachable M₁ M₂) (h₂ : N.Reachable M₂ M₃) : N.Reachable M₁ M₃ := by
  induction h₁ with
  | refl        => exact h₂
  | step hen _ ih => exact .step hen (ih h₂)

end Reachable

end PTNet

end Cslib.PetriNet
