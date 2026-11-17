# Mathlib

This folder contains `.lean` files with declarations missing from the current version of Mathlib.
Its tree mirrors Mathlib's file structure: `Mathlib/X/Y.lean` holds the declarations whose
eventual home is the Mathlib file `Mathlib/X/Y.lean`, and imports that file when it exists. The
declarations that only the Archive uses are mirrored in the same way in
[`../Archive/Mathlib`](../Archive/Mathlib).
