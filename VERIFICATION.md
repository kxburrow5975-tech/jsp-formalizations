# Verification

Toolchain: Lean 4.34.0 (`lean-toolchain`).
Command: `lake build`.
No Mathlib. No `sorry`.

| Theorem | Axioms |
| --- | --- |
| `JSP000307.theorem_jsp_000307` | `propext` |
| `JSP000301.theorem_jsp_000301` | `propext`, `Quot.sound` |

JSP-000307 matches the catalog wording as currently published (existence of one descending triple). Infinitude (Erdős #372 / Balog) is out of scope.

JSP-000301 independently checks the classical Golomb/Walker/Guy witness. It does not claim first formalization priority.
