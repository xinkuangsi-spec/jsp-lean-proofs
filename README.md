# jsp-lean-proofs

Lean 4 + Mathlib formalizations for problems from the
[Justin Sun Prize](https://github.com/TheJustinSunPrize/awards) problem bank.
One self-contained file per problem under `JspProofs/`.

## Contents

| Problem | File | Statement | Result |
|---|---|---|---|
| JSP-000288 | `JspProofs/Jsp000288.lean` | Must ratios of consecutive terms in the specified minimal stably complete sequences converge to the golden ratio? | **No** — an explicit lacunary strongly-complete sequence (growth ratio ≥ 6/5, complete after any finite deletion, not complete after a specified infinite deletion) whose consecutive quotients do not converge. Final theorem: `jsp_000288_answer`. |
| JSP-000884 | `JspProofs/Jsp000884.lean` | How does an integer's totient compare with the totient of the integer minus its totient? | Each of the three comparisons `φ(n) ⋚ φ(n−φ(n))` holds for infinitely many `n` (explicit families `2^{k+2}`, `3·2^{k+1}`, `15·2^{k+1}`). Final theorem: `jsp_000884_answer`. |
| JSP-000945 | `JspProofs/Jsp000945.lean` | Is there an integer whose differences from twice every permitted smaller square are all prime? | **Yes** — `n = 199` (and all 8 known values verified). Final theorem: `jsp_000945_answer`. |

## Build

```
lake build
```

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`.
No `sorry`, no additional axioms (only `propext`, `Classical.choice`,
`Quot.sound`).
