# constructible-universe
Formalization of Gödel's constructible universe in Lean 4

## Structure
* `Constructible.lean`: Library gateway.
* `Constructible/Basic.lean`: Lists and some other basics.
* `Constructible/LHierarchy.lean`: The $L_\alpha$ hierarchy defined. (Main definition is in the
segment starting at line 833, using the mutual inductive definition of codes for elements of $L$ given in lines 144--235. The outline is described in comments at those points.)
* `Constructible/Extensionality.lean`: Proof of the Axiom of Extensionality in $L$.

## Current Status: **Work in Progress**

**Note:** The code is provided for research and review purposes.

### To-Do List:
- [ ] Prove the ZFC + GCH axioms (assuming the base wellorder has the right sort of length)
- [ ] Prove $\omega_1^{\mathrm{ck}}$ is the least ordinal $\gamma$ such that $L_\gamma$ models KP

## Build
```bash
lake exe cache get
lake build

## Author
* **Farmer Schlutzenberg** - *Initial formalization and development* - [farmerss](https://github.com/farmerss) | [Website](https://sites.google.com/site/schlutzenberg)