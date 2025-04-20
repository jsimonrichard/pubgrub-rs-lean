import Mathlib
import Std.Data.HashMap

open Std

variable (P : Type) [BEq P] [Hashable P]
variable (V : Type) [Ord V]

def DependencyConstraints : Type :=
  HashMap P (Set V)

inductive Dependencies (M : Type) where
  | Unavailable (m : M)
  | Available (constraints : DependencyConstraints P V)

structure PackageResolutionStatistics where
  unitPropagationAffected : Nat
  unitPropagationCulprit : Nat
  dependenciesAffected : Nat
  dependenciesCulprit : Nat

def PackageResolutionStatistics.conflictCount (s : PackageResolutionStatistics) : Nat :=
  s.unitPropagationAffected + s.unitPropagationCulprit + s.dependenciesAffected + s.dependenciesCulprit

class DependencyProvider (α : Type) where
  P : Type
  [beqP : BEq P]
  [hashableP : Hashable P]
  V : Type
  [ordV : Ord V]
  E : Type
  Priority : Type
  [ordPriority : Ord Priority]

  -- Message type
  M : Type

  prioritize : α → P → Set V → PackageResolutionStatistics → Priority
  chooseVersion : α → P → Set V → Except E (Option V)
  getDependencies : α → P → V → Except E (Dependencies P V M)

  -- If this returns an error, the solver will stop.
  -- Otherwise, we'll keep going.
  shouldCancel : α → Except E Unit
