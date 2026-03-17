# constructible-universe
Formalization of Gödel's constructible universe in Lean 4

## Structure
* `Constructible.lean`: Library gateway.
* `Constructible/Basic.lean`: Lists and some other basics.
* `Constructible/LHierarchy.lean`: The $L_\alpha$ hierarchy defined. (Main definition is in the
segment starting at line 836, using the mutual inductive definition of codes for elements of $L$ given in lines 138--227. The outline is described in comments at those points.)
* `Constructible/Extensionality.lean`: Proof of the Axiom of Extensionality in $L$.

## Current Status: **Work in Progress**

**Note:** The code is provided for research and review purposes, but it won't
compile successfully with `lake build` at this exact moment.

### To-Do List:
- [ ] Fix proofs of lemmas in connection with variable substitution

## Build (when ready)
```bash
lake exe cache get
lake build

## Author
* **Farmer Schlutzenberg** - *Initial formalization and development* - [farmerss](https://github.com/farmerss) | [Website](https://sites.google.com/site/schlutzenberg)