# CaTTExp

Design exploration toward a user-friendly proof assistant in the style of
CaTT, the type theory for globular weak ω-categories (Finster–Mimram). The
long-term aim is something like an internal language for the ω-category of
ω-categories, built from rules in the aesthetic of the published CaTT
variants.

Layout:

- `notes/`: design notes and literature surveys.
- `notes/open-issues.md`: the single list of known open items, each with its owner and status. Threads update it whenever they find or close an item.
- `src/`: Agda formalization experiments.

## Building the Agda development

Requires Agda 2.6.3 or later; there is no standard library dependency.

```
cd src
LC_ALL=C.UTF-8 agda Everything.agda
```

`src/CaTTExp/` contains core CaTT (syntax, typing, pasting contexts, a
certified checker), worked examples, and exploratory sketches under
`Sketch/`. Design findings from the sketches are in `notes/`.
