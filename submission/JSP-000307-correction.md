# Paste into https://github.com/TheJustinSunPrize/awards/issues/new

Title: [Correction] JSP-000307: kernel-checked Lean existence proof (14, 15, 16)

### Record or document

`problems/catalog-0301-0400.md` — section `JSP-000307`
Also the matching row in `problems/README.md`.

### Current text and proposed correction

Current Lean proof: No.

Proposed, if the published existence wording is kept:
- Lean proof: Yes — https://github.com/kxburrow5975-tech/jsp-formalizations @ `2626cf99977f288f93dd5fc348e60f22494a7cfb`, theorem `JSP000307.theorem_jsp_000307`
- Eligible to claim: Yes (Solved + Lean Yes)
- Claim status: Unclaimed

This is not a proof of infinitude. See awards#14. If infinitude is restored, this file does not close the record.

### Evidence and affected records

- Repository: https://github.com/kxburrow5975-tech/jsp-formalizations
- Pinned commit: `2626cf99977f288f93dd5fc348e60f22494a7cfb`
- File: `JspFormalizations/JSP000307.lean`
- Toolchain: Lean 4.34.0, no Mathlib
- Build: `lake build`; axioms: `propext` only
- Related: awards#14, awards#68

### Relevant conflicts

None. Formalization only.
