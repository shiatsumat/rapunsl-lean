---
name: proof-polish
description: Final polish pass for tactic proofs in the rapunsl-lean repo. Use this after getting a proof to compile — before presenting or committing it — whenever writing or editing Lean proofs in this repository, even if the user only asks to "prove X" without mentioning cleanup.
---

# Proof polish (rapunsl-lean)

Once a proof compiles, give it a formatting pass before considering it done. Match the existing style in files like `RBI/Add.lean`.

## No floating short tactics

A very short tactic step (like a lone `rw [hC];`) should not float on its own line — a one-word line reads as visually "floating". Append it to the preceding line with a `;` separator, keeping line lengths reasonable.

**Example:**

```lean
-- Avoid
rcases mem with ⟨f, cohf⟩
rw [hC]
exact cohf a mem'

-- Prefer
rcases mem with ⟨f, cohf⟩; rw [hC]
exact cohf a mem'
```
