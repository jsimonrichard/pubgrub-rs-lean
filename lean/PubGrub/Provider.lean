import PubGrub.Solver
import Std.Data.HashMap
import Std.Data.TreeMap

open Std

variable (P : Type) [Package P]
variable (V : Type) [Ord V]

structure OfflineDependencyProvider where
  dependencies : HashMap P (TreeMap V (DependencyConstraints P V))

namespace OfflineDependencyProvider

def new : OfflineDependencyProvider P V :=
  { dependencies := HashMap.emptyWithCapacity }

def addDependencies (self : OfflineDependencyProvider P V) (package : P) (version : V)
  (dependencies : DependencyConstraints P V) : OfflineDependencyProvider P V :=
  { dependencies := self.dependencies.insert package (
    (self.dependencies.getD package .empty).insert version dependencies
  ) }

def packages (self : OfflineDependencyProvider P V) : List P :=
  self.dependencies.keys

def versions (self : OfflineDependencyProvider P V) (package : P) : List V :=
  self.dependencies.getD package .empty |>.keys

def getDependencies (self : OfflineDependencyProvider P V) (package : P) (version : V) : Option $ DependencyConstraints P V :=
  self.dependencies.getD package .empty |>.get? version

end OfflineDependencyProvider

instance : DependencyProvider (OfflineDependencyProvider P V) where
  P := P
  V := V
  E := Empty
  Priority := Nat
  M := String
  chooseVersion := fun self package vs =>
    let versions := self.dependencies.getD package .empty
    versions.keys.find? fun v => (vs v)
