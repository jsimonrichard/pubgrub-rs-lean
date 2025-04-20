import Std
import PubGrub.VersionSet

variable [Ord V]

inductive Bound (v : Type) [Ord V] where
  | Included (v : V)
  | Excluded (v : V)
  | Unbounded
deriving BEq

structure Segment (v : Type) [Ord v] where
  left : Bound V
  right : Bound V
  wellFormed : match left, right with
    | Bound.Included v1, Bound.Included v2 => (compare v1 v2).isLE
    | Bound.Included v1, Bound.Excluded v2 => compare v1 v2 = .le
    | Bound.Excluded v1, Bound.Included v2 => compare v1 v2 = .lt
    | Bound.Excluded v1, Bound.Excluded v2 => compare v1 v2 = .le
    | _, _ => True
deriving BEq

class StrictPartialOrder (α : Type) where
  lt : α → α → Prop
  lt_irrefl : ∀ a : α, ¬lt a a
  lt_trans : ∀ a b c : α, lt a b → lt b c → lt a c

instance [StrictPartialOrder α] : LT α := ⟨StrictPartialOrder.lt⟩


instance : StrictPartialOrder (Segment V) where
  lt := λ s1 s2 => (
    match s1.right, s2.left with
    | Bound.Included v1, Bound.Included v2 => (compare v1 v2).isLT
    | Bound.Excluded v1, Bound.Included v2 => (compare v1 v2).isLE
    | Bound.Included v1, Bound.Excluded v2 => (compare v1 v2).isLE
    | _, _ => False
  )
/-- Ranges represents multiple intervals of a continuous range of monotone increasing values.

    Invariants:
    1. The segments are sorted, from lowest to highest
    2. Each segment contains at least one version (start < endBound)
    3. There is at least one version between two segments -/
structure Ranges (V : Type) [Ord V] where
  segments : List (Segment V)
deriving BEq

namespace Ranges

def empty [Ord V] : Ranges V where
  segments := []

def full [Ord V] : Ranges V where
  segments := [{ left := Bound.Unbounded, right := Bound.Unbounded }]

def singleton (v : V) : Ranges V where
  segments := [{ left := Bound.Included v, right := Bound.Included v }]

def contains (v : V) (r : Ranges V) : Bool :=
  r.segments.any fun s => match s.left, s.right with
    | Bound.Included v1, Bound.Included v2 =>
      (compare v1 v).isLE && (compare v v2).isLE
    | Bound.Included v1, Bound.Excluded v2 =>
      (compare v1 v).isLE && (compare v v2).isLT
    | Bound.Excluded v1, Bound.Included v2 =>
      (compare v1 v).isLT && (compare v v2).isLE
    | Bound.Excluded v1, Bound.Excluded v2 =>
      (compare v1 v).isLT && (compare v v2).isLT
    | Bound.Unbounded, Bound.Included v2 =>
      (compare v v2).isLE
    | Bound.Unbounded, Bound.Excluded v2 =>
      (compare v v2).isLT
    | Bound.Included v1, Bound.Unbounded =>
      (compare v1 v).isLE
    | Bound.Excluded v1, Bound.Unbounded =>
      (compare v1 v).isLT
    | Bound.Unbounded, Bound.Unbounded => true

def negateSegments (start : Bound V) (segments : List (Segment V)) : Ranges V := Id.run do
  let mut complementSegments := []
  let mut start := start
  for s in segments do
    complementSegments := complementSegments ++ List.singleton (
      ⟨
        start, match s.left with
        | Bound.Included v => Bound.Excluded v
        | Bound.Excluded v => Bound.Included v
        | Bound.Unbounded => Bound.Unbounded⟩: Segment V
    )
    start := s.right
  if start != Bound.Unbounded then
    complementSegments := complementSegments.push ⟨start, Bound.Unbounded⟩
  .mk complementSegments


def complement (r : Ranges V) : Ranges V :=
  match r.segments with
    | [] => full
    | s :: ss =>
      match s.left, s.right with
      | .Unbounded, .Unbounded => empty
      | .Included v1, .Unbounded => .mk [⟨.Unbounded, .Excluded v1⟩]
      | .Excluded v1, .Unbounded => .mk [⟨.Unbounded, .Included v1⟩]
      | .Unbounded, .Included v2 => negateSegments (Bound.Excluded v2) ss
      | .Unbounded, .Excluded v2 => negateSegments (Bound.Included v2) ss
      | .Included _, .Included _
      | .Included _, .Excluded _
      | .Excluded _, .Included _
      | .Excluded _, .Excluded _ => negateSegments .Unbounded ss

def intersection (r1 r2 : Ranges V) : Ranges V :=
  -- TODO: Implement intersection by finding overlapping segments
  sorry

instance : VersionSet (Ranges V) where
  V := V
  empty := empty
  singleton := singleton
  contains := contains
  complement := complement
  intersection := intersection

end Ranges
