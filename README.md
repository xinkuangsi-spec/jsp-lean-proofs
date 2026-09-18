# jsp-lean-proofs

Lean 4 + Mathlib formalizations for problems from the
[Justin Sun Prize](https://github.com/TheJustinSunPrize/awards) problem bank.
One self-contained file per problem under `JspProofs/`.

## Contents

| Problem | File | Statement | Result |
|---|---|---|---|
| JSP-000288 | `JspProofs/Jsp000288.lean` | Must ratios of consecutive terms in the specified minimal stably complete sequences converge to the golden ratio? | **No** — an explicit lacunary strongly-complete sequence (growth ratio ≥ 6/5, complete after any finite deletion, not complete after a specified infinite deletion) whose consecutive quotients do not converge. Final theorem: `jsp_000288_answer`. |

## Build

```
lake build
```

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`.
No `sorry`, no additional axioms (only `propext`, `Classical.choice`,
`Quot.sound`).
