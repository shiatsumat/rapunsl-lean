---
name: commit-style
description: Commit-message conventions for the rapunsl-lean repo. Use this whenever writing, amending, or suggesting a git commit message in this repository, even if the user only says "commit this" without mentioning message style.
---

# Commit message style (rapunsl-lean)

Subject lines follow the repo's terse imperative style, e.g. `Prove add_assoc`, `Tweak to add_pointwise`, `Add coher_add'/coher_add in RBI.Add`. Check `git log --oneline` for the current tone before writing.

## Refer to files by module name, not file name

Write `RBI.Add` or `Math.Algebra.RR`, never `Add.lean`. Bare file names are ambiguous — several directories could plausibly contain an `Add.lean` — while the dotted module path is unique and matches how the user refers to files.

**Example:** `Add add_satis in RBI.Add`, not `Add add_satis in Add.lean`.

## Collapse shared prefixes when listing lemmas

When the subject enumerates several declarations sharing a common name prefix, write the prefix once and slash-separate the suffixes. This keeps subject lines compact.

**Example:** `Add add_exists/or/false in RBI.Add`, not `Add add_exists/add_or/add_false in RBI.Add`.

## Name only the main deliverable

Don't enumerate secondary changes such as auxiliary library lemmas added along the way.

**Example:** `Add add_instUnambig in RBI.Add`, not `Add add_instUnambig in RBI.Add, with add_incomp lemmas in RR`.
