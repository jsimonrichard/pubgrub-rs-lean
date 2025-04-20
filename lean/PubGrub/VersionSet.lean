class VersionSet (VS : Type) [BEq VS] where
  V : Type
  [ordV : Ord V]
  empty : VS
  singleton : V → VS

  contains : V → VS → Bool
  complement : VS → VS
  intersection : VS → VS → VS
  union : VS → VS → VS :=
    fun s1 s2 => complement (intersection (complement s1) (complement s2))
  full : VS := complement empty

  isDisjoint : VS → VS → Bool :=
    fun s1 s2 => (intersection s1 s2) == empty
  subsetOf : VS → VS → Bool :=
    fun s1 s2 => s1 == (intersection s1 s2)
