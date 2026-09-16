# jsp-formalizations

Independent Lean 4 (v4.34.0) formalizations for two Justin Sun Prize catalog
problems. No Mathlib. No `sorry`.

| ID | Theorem | Axioms | Status |
| --- | --- | --- | --- |
| JSP-000307 | `JSP000307.theorem_jsp_000307` | `propext` | `lake build` |
| JSP-000301 | `JSP000301.theorem_jsp_000301` | `propext`, `Quot.sound` | `lake build` |

## Claims

- **JSP-000307.** There exist three consecutive positive integers with strictly decreasing largest prime factors. Witness: 14, 15, 16 (factors 7, 5, 2).
- **JSP-000301.** There exist consecutive powerful nonsquares. Witness: 12167 = 23³ and 12168 = 2³·3²·13². Classical counterexample (Golomb / Walker / Guy). This repo does not claim mathematical discovery.

Mathematical authorship and Lean authorship are distinct. A successful kernel check is not an award or a right to payment.

## Build

```
elan toolchain install leanprover/lean4:v4.34.0
lake build
```

## Prize note

File Correction / Recipient issues on [TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards) under the payee's own GitHub identity. Use `RECIPIENT-` placeholders until written confirmation.
