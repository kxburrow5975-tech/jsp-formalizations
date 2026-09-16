# Paste into https://github.com/TheJustinSunPrize/awards/issues/new

Title: [Correction] JSP-000301: independent kernel-checked Lean counterexample (12167, 12168)

### Record or document

`problems/catalog-0301-0400.md` — section `JSP-000301`

### Current text and proposed correction

Lean proof is currently No. Independent kernel-checked source of the catalog witness:

- Lean proof: Yes — https://github.com/kxburrow5975-tech/jsp-formalizations @ `2626cf99977f288f93dd5fc348e60f22494a7cfb`, theorem `JSP000301.theorem_jsp_000301`

Does not claim first-formalization priority. See awards#25 and awards#94.

### Evidence and affected records

- Repository: https://github.com/kxburrow5975-tech/jsp-formalizations
- Pinned commit: `2626cf99977f288f93dd5fc348e60f22494a7cfb`
- File: `JspFormalizations/JSP000301.lean`
- Toolchain: Lean 4.34.0, no Mathlib
- Build: `lake build`; axioms: `propext`, `Quot.sound`

### Relevant conflicts

None. Formalization of a classical counterexample only.
