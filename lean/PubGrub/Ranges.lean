import Std
import PubGrub.VersionSet
import Mathlib
import PubGrub.TransitivityBFS

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

instance : BEq (Segment V) where
  beq s1 s2 := s1.left == s2.left && s1.right == s2.right

namespace Segment

def contains (v : V) (s : Segment V) : Bool :=
  (match s.left with
  | Bound.Included v1 => (compare v1 v).isGE
  | Bound.Excluded v1 => (compare v1 v).isGT
  | Bound.Unbounded => True) &&
  (match s.right with
  | Bound.Included v2 => (compare v v2).isLE
  | Bound.Excluded v2 => (compare v v2).isLT
  | Bound.Unbounded => True)

end Segment


class StrictPartialOrder (α : Type) where
  lt : α → α → Prop
  lt_irrefl : ∀ a : α, ¬lt a a
  lt_trans : ∀ a b c : α, lt a b → lt b c → lt a c

instance [StrictPartialOrder α] : LT α := ⟨StrictPartialOrder.lt⟩

lemma Ordering.lt_eq_iff_not_ge (o : Ordering) : o = lt ∨ o = eq ↔ o ≠ gt := by
  constructor
  . intro h
    cases o
    all_goals simp
    cases h
    all_goals simp_all
  . intro h
    cases o
    all_goals simp
    apply h
    simp



instance : StrictPartialOrder (Segment V) where
  lt s1 s2 := (
    match s1.right, s2.left with
    | Bound.Included v1, Bound.Included v2 => (compare v1 v2).isLT
    | Bound.Excluded v1, Bound.Included v2 => (compare v1 v2).isLE
    | Bound.Included v1, Bound.Excluded v2 => (compare v1 v2).isLE
    | Bound.Excluded v1, Bound.Excluded v2 => (compare v1 v2).isLE
    | _, _ => False
  )
  lt_irrefl s := by
    rcases s with ⟨left, right, wellFormed⟩

    cases right
    all_goals cases left
    all_goals simp at wellFormed
    all_goals simp_all -- handles Unbounded cases

    . rw [Bool.eq_false_iff]
      intro h
      rw [Ordering.isLT_iff_eq_lt, compare_lt_iff_lt] at h
      absurd h
      simp [wellFormed]

    all_goals rw [compare_gt_iff_gt]
    all_goals simp [wellFormed]

  lt_trans s1 s2 s3 h12 h23 := by
    rcases s1 with ⟨_, b1, _⟩
    rcases s2 with ⟨b2, b3, wellFormed⟩
    rcases s3 with ⟨b4, _, _⟩

    cases b1
    all_goals cases b2
    all_goals cases b3
    all_goals cases b4

    all_goals simp_all
    all_goals simp at wellFormed

    any_goals rw [Ordering.isLT_iff_eq_lt, compare_lt_iff_lt] at *
    any_goals rw [
      Ordering.isLE_iff_eq_lt_or_eq_eq,
      Ordering.lt_eq_iff_not_ge,
      compare_le_iff_le
    ] at *

    all_goals solve_ineq_chain

instance [StrictPartialOrder α] : LT α := ⟨StrictPartialOrder.lt⟩

/-- Ranges represents multiple intervals of a continuous range of monotone increasing values.

    Invariants:
    1. The segments are sorted, from lowest to highest
    2. Each segment contains at least one version (start < endBound)
    3. There is at least one version between two segments -/
structure Ranges (V : Type) [LinearOrder V] where
  segments : List (Segment V)
  sorted : List.Sorted (· < ·) segments

instance : BEq (Ranges V) where
  beq r1 r2 := r1.segments == r2.segments

namespace Ranges

def empty : Ranges V where
  segments := []
  sorted := by simp [List.Sorted]

def full : Ranges V where
  segments := [⟨Bound.Unbounded, Bound.Unbounded, by simp⟩]
  sorted := by simp [List.Sorted]

def singleton (v : V) : Ranges V where
  segments := [⟨Bound.Included v, Bound.Included v, by simp⟩]
  sorted := by simp [List.Sorted]

def contains (v : V) (r : Ranges V) : Bool :=
  r.segments.any fun s => s.contains v

def prepend (s : Segment V) (r : Ranges V) (h : ∀ s' ∈ r.segments, s < s') : Ranges V :=
  ⟨
    s :: r.segments,
    List.pairwise_cons.mpr ⟨h, r.sorted⟩
  ⟩


def negate_segs_right (r : Ranges V) : Ranges V
  :=
    sorry

  -- Id.run do
  -- let mut complementSegments := []
  -- let mut start := start
  -- for s in r.segments do
  --   complementSegments := complementSegments ++ List.singleton (
  --     ⟨
  --       start, match s.left with
  --       | Bound.Included v => Bound.Excluded v
  --       | Bound.Excluded v => Bound.Included v
  --       | Bound.Unbounded => Bound.Unbounded,
  --       by simp
  --     ⟩
  --   )
  --   start := s.right
  -- if start != Bound.Unbounded then
  --   complementSegments := complementSegments.push ⟨start, Bound.Unbounded⟩
  -- .mk complementSegments

-- def prependToSorted {α} [LT α] (x : α) (xs : List α) (hs : List.Sorted (· < ·) xs)
--   (h : (ne : xs ≠ []) → x < xs.head ne) : List.Sorted (· < ·) (x :: xs) := by
--   simp [List.Sorted]
--   constructor
--   .
--   . exact hs

lemma head_gt_negate_segs_right (r : Ranges V) (hr : r.segments ≠ []) :
  ∀ s' ∈ r.negate_segs_right.segments, (r.segments.head hr) < s'
  := by
  intro s' hs
  sorry




def complement (r : Ranges V) : Ranges V :=
  match hrs : r.segments with
    | [] => full
    | s :: ss =>
      match s.left, s.right with
      | .Unbounded, .Unbounded => empty
      | .Included v1, .Unbounded => .mk
        [⟨.Unbounded, .Excluded v1, by simp⟩]
        (by simp)
      | .Excluded v1, .Unbounded => .mk
        [⟨.Unbounded, .Included v1, by simp⟩]
        (by simp)
      | .Unbounded, .Included v2 => negate_segs_right r
      | .Unbounded, .Excluded v2 => negate_segs_right r
      | .Included v1, _ => Id.run do
        let rc := negate_segs_right r
        let sc := ⟨.Unbounded, .Excluded v1, by simp⟩
        have r := ⟨ s :: ss, r.sorted ⟩
        let h := head_gt_negate_segs_right r (by
          intro h2
          absurd List.cons_ne_nil s ss
          rw [← hrs]
          exact h2
        )
        Ranges.prepend sc rc (by
          intro s' hs

        )
      | .Excluded _, _ => sorry

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
