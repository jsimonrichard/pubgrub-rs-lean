structure SemanticVersion where
  major : Nat
  minor : Nat
  patch : Nat
deriving DecidableEq, Repr

instance : Ord SemanticVersion where
  compare v1 v2 :=
    let mj := compare v1.major v2.major
    if mj != .eq then
      mj
    else
    let mn := compare v1.minor v2.minor
    if mn != .eq then
      mn
    else
      compare v1.patch v2.patch


namespace SemanticVersion

def zero : SemanticVersion :=
  { major := 0, minor := 0, patch := 0 }


def one : SemanticVersion :=
  { major := 1, minor := 0, patch := 0 }

def two : SemanticVersion :=
  { major := 2, minor := 0, patch := 0 }

def bumpPatch (v : SemanticVersion) : SemanticVersion :=
  { v with patch := v.patch + 1 }

def bumpMinor (v : SemanticVersion) : SemanticVersion :=
  { v with minor := v.minor + 1 }

def bumpMajor (v : SemanticVersion) : SemanticVersion :=
  { v with major := v.major + 1 }

end SemanticVersion
