import Mathlib

open Lean Meta Elab Tactic Std

/--
`sovle_ineq_chain` tries to solve goals of the form `a < b` or `a ≤ b`
by chaining together hypotheses of the form `x < y` or `x ≤ y`.
-/
partial def loop (queue : Array (Expr × Array (Expr × Name)))
       (visited : HashSet Expr)
       (edges : Array (Expr × Name × Expr × Expr))
       (rhs : Expr)
       : MetaM (Option (Array (Expr × Name))) := do
    if queue.isEmpty then
      return none
    let (curr, path) := queue[0]!
    let queue := queue.eraseIdx! 0
    if curr == rhs then
      return some path
    if visited.contains curr then
      return (← loop queue visited edges rhs)
    let visited := visited.insert curr
    let mut newQueue := queue
    for (h, rel, x, y) in edges do
      if x == curr then
        newQueue := newQueue.push (y, path.push (h, rel))
    loop newQueue visited edges rhs

elab "solve_ineq_chain" : tactic => do
  let goal ← getMainGoal
  let tgt ← getMainTarget
  -- Parse the goal: expect `a < b` or `a ≤ b`
  let (goalRel, lhs, rhs) ←
    match tgt.getAppFnArgs with
    | (``LT.lt, #[_, _, lhs, rhs]) => pure (`lt, lhs, rhs)
    | (``LE.le, #[_, _, lhs, rhs]) => pure (`le, lhs, rhs)
    | _ => throwError "Goal is not a strict or non-strict inequality"
  -- Collect all hypotheses of the form `x < y` or `x ≤ y`
  let lctx ← getLCtx
  let mut edges : Array (Expr × Name × Expr × Expr) := #[]
  for localDecl in lctx do
    if !localDecl.isImplementationDetail then
      let type := localDecl.type
      match type.getAppFnArgs with
      | (``LT.lt, #[_, _, x, y]) =>
        edges := edges.push (localDecl.toExpr, `lt, x, y)
      | (``LE.le, #[_, _, x, y]) =>
        edges := edges.push (localDecl.toExpr, `le, x, y)
      | _ => pure ()

  -- BFS to find a path from lhs to rhs
  -- Each node: (current expr, path of (hyp, rel))
  let mut queue : Array (Expr × Array (Expr × Name)) := #[(lhs, #[])]
  let mut visited : HashSet Expr := {}

  let found ← loop queue visited edges rhs
  match found with
  | none => throwError "Could not find a chain of inequalities"
  | some path =>
    -- Build the proof by applying transitivity along the path
    if goalRel == `lt && !path.any (fun (_, rel) => rel == `lt) then
      throwError "No strict inequality in the chain"

    let mut prf := path[0]!.1
    let mut prfRel := path[0]!.2
    for i in [1:path.size] do
      let (h, rel) := path[i]!
      prf ← match (prfRel, rel) with
        | (`lt, `lt) => mkAppM ``lt_trans #[prf, h]
        | (`lt, `le) => mkAppM ``lt_of_lt_of_le #[prf, h]
        | (`le, `lt) =>
          prfRel := `lt
          mkAppM ``lt_of_le_of_lt #[prf, h]

        | (`le, `le) => mkAppM ``le_trans #[prf, h]
        | _ => throwError "Unknown relation"
    -- For < goals, if the last step is le, use le_of_lt
    if goalRel == `le && path.any (fun (_, rel) => rel == `lt) then
      prf ← mkAppM ``le_of_lt #[prf]
    goal.assign prf


example (a b c d e : Nat)
  (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) (h4 : d < e)
  : a < e := by
  -- solve_ineq_chain
  linarith

variable [LinearOrder V] [BEq V]

example (v1 v2 v3 v4 : V)
  (wellFormed : v3 ≤ v2)
  (h12 : v4 < v3)
  (h23 : v2 < v1)
  : v4 < v1 := by
  solve_ineq_chain
  -- linarith
