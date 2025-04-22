import Std
import PubGrub.VersionSet
import Mathlib

variable [LinearOrder V] [BEq V]

inductive Bound (V : Type) [LinearOrder V] where
  | Included (v : V)
  | Excluded (v : V)
  | Unbounded
deriving BEq

structure Segment (V : Type) [LinearOrder V] where
  left : Bound V
  right : Bound V
  wellFormed : match left, right with
    | (Bound.Included v1), (Bound.Included v2) => v1 ≤ v2
    | (Bound.Included v1), (Bound.Excluded v2)
    | (Bound.Excluded v1), (Bound.Included v2)
    | (Bound.Excluded v1), (Bound.Excluded v2) => v1 < v2
    | _, _ => True
    := by simp_all only; rfl


instance : BEq (Segment V) where
  beq s1 s2 := s1.left == s2.left && s1.right == s2.right

class StrictPartialOrder (α : Type) where
  lt : α → α → Prop
  lt_irrefl : ∀ a : α, ¬lt a a
  lt_trans : ∀ a b c : α, lt a b → lt b c → lt a c

instance [StrictPartialOrder α] : LT α := ⟨StrictPartialOrder.lt⟩

instance : StrictPartialOrder (Segment V) where
  lt s1 s2 := (
    match s1.right, s2.left with
    | Bound.Included v1, Bound.Included v2 => v1 < v2
    | Bound.Excluded v1, Bound.Included v2 => v1 ≤ v2
    | Bound.Included v1, Bound.Excluded v2 => v1 ≤ v2
    | _, _ => False
  )
  lt_irrefl s := by
    cases s with
    | mk left right wellFormed =>
      cases right
      all_goals simp_all -- handles Unbounded cases
      case Included v1 =>
        cases left
        all_goals simp at wellFormed
        all_goals simp_all -- handles Unbounded cases

      case Excluded v1 =>
        cases left
        all_goals simp at wellFormed
        all_goals simp_all -- handles Unbounded and Excluded cases

  lt_trans s1 s2 s3 h12 h23 := by
    cases s1 with
    | mk _ b1 _ =>
      cases b1
      cases s2 with
      | mk b2 b3 wellFormed =>
        cases b2
        cases b3
        cases s3 with
        | mk b4 _ _ =>
          cases b4
          all_goals simp at wellFormed
          all_goals simp_all
          case mk.Included.mk.Included.Included.mk.Included v4 _ v3 v2 _ v1 _ =>
            have h' : v3 < v1 := by
              apply lt_of_le_of_lt
              exact wellFormed
              exact h23
            trans v3
            . exact h12
            . exact h'

          case mk.Included.mk.Included.Included.mk.Excluded v4 _ v3 v2 _ v1 _ =>
            sorry




/-- Ranges represents multiple intervals of a continuous range of monotone increasing values.

    Invariants:
    1. The segments are sorted, from lowest to highest
    2. Each segment contains at least one version (start < endBound)
    3. There is at least one version between two segments -/
structure Ranges (V : Type) [LinearOrder V] where
  segments : List (Segment V)
deriving BEq

namespace Ranges

def empty : Ranges V where
  segments := []

def full : Ranges V where
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
