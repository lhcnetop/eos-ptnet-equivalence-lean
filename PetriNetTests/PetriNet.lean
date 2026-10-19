/-
Copyright (c) 2025 Luis Henrique Costa Neto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luis Henrique Costa Neto
-/
import PetriNet.Semantics

/-!
# Tests for `PTNet`, `Enabled`, `fire`, `Reachable`, and LTS semantics.

Two concrete nets are used: `loopNet` (single-place self-loop) and `transferNet`
(two-place token transfer).
-/

namespace CslibTests

open Cslib.PetriNet
open Cslib.PetriNet.PTNet

/-! ### loopNet: single place `Unit`, single transition `Unit` -/

def loopNet : PTNet Unit Unit where
  pre  _ _ := 1
  post _ _ := 1

-- Enabled in a marking with one token.
example : loopNet.Enabled (fun _ => 1) () := by decide

-- Firing the loop transition preserves the token count.
example : loopNet.fire (fun _ => 1) () = fun _ => 1 := by
  funext p; cases p; simp [loopNet]

-- Token balance at the single place.
example (p : Unit) :
    loopNet.fire (fun _ => 1) () p + loopNet.pre () p =
    (fun _ => 1 : Marking Unit) p + loopNet.post () p := by
  cases p; simp [loopNet]

-- Enabledness is monotone: one token → two tokens still enables the transition.
example : loopNet.Enabled (fun _ => 2) () :=
  Enabled.mono loopNet (show loopNet.Enabled (fun _ => 1) () from by decide)
    (fun p => by cases p; omega)

-- The LTS transition holds between two equal markings.
example : loopNet.toLTS.Tr (fun _ => 1) () (fun _ => 1) :=
  ⟨by decide, by funext p; cases p; simp [loopNet]⟩

-- The LTS of loopNet is deterministic.
example : loopNet.toLTS.Deterministic := inferInstance

-- A single enabled firing yields reachability in one step.
example : loopNet.Reachable (fun _ => 1) (loopNet.fire (fun _ => 1) ()) :=
  Reachable.single (t := ()) (by decide)

-- Reachability is transitive.
example : loopNet.Reachable (fun _ => 1) (fun _ => 1) := by
  have hfire : loopNet.fire (fun _ => 1) () = fun _ => 1 := by
    funext p; cases p; simp [loopNet]
  have step : loopNet.Reachable (fun _ => 1) (fun _ => 1) :=
    hfire ▸ Reachable.single (t := ()) (by decide)
  exact step.trans step

/-! ### transferNet: two places `Bool`, single transition `Unit` -/

/-- A net with source place `false` and destination place `true`.
The single transition consumes one token from `false` and produces one in `true`. -/
def transferNet : PTNet Bool Unit where
  pre  _ | false => 1 | true => 0
  post _ | false => 0 | true => 1

def initMark : Marking Bool
  | false => 1
  | true  => 0

def targetMark : Marking Bool
  | false => 0
  | true  => 1

-- The transfer is enabled in the initial marking.
example : transferNet.Enabled initMark () := by decide

-- The transfer is NOT enabled in the zero marking.
example : ¬ transferNet.Enabled (fun _ => 0) () := by decide

-- Firing moves the token from source to destination.
example : transferNet.fire initMark () = targetMark := by decide

-- Token balance at the source place.
example :
    transferNet.fire initMark () false + transferNet.pre () false =
    initMark false + transferNet.post () false := by decide

-- The target marking is reachable from the initial marking.
example : transferNet.Reachable initMark targetMark := by
  have hfire : transferNet.fire initMark () = targetMark := by decide
  exact hfire ▸ Reachable.single (t := ()) (by decide)

-- Equivalence with LTS reachability.
example : transferNet.toLTS.CanReach initMark targetMark := by
  rw [← reachable_iff_canReach]
  have hfire : transferNet.fire initMark () = targetMark := by decide
  exact hfire ▸ Reachable.single (t := ()) (by decide)

-- The LTS of transferNet is deterministic.
example : transferNet.toLTS.Deterministic := inferInstance

end CslibTests
