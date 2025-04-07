#!/bin/bash

../aeneas/charon/bin/charon --opaque crate::internal::small_map --hide-marker-traits
../aeneas/bin/aeneas -backend lean pubgrub.llbc -dest lean