# CaTTExp

Design exploration toward a user-friendly proof assistant in the style of
CaTT, the type theory for globular weak ω-categories (Finster–Mimram). The
long-term aim is something like an internal language for the ω-category of
ω-categories, built from rules in the aesthetic of the published CaTT
variants.

Layout:

- `spec/`: the consolidated specification of the system as it currently stands, one file per chapter, with the kernel and the surface kept apart. It states only current answers and cites `notes/`.
- `notes/`: design notes and literature surveys. This is the research record.
- `notes/open-issues.md`: the single list of known open items, each with its owner and status. Threads update it whenever they find or close an item.
- `src/`: Agda formalization experiments.

## Building the Agda development

Requires Agda 2.6.3 or later; there is no standard library dependency.

```
cd src
LC_ALL=C.UTF-8 agda +RTS -M12G -RTS Everything.agda
```

The full check needs a larger heap than Agda's default (it runs out at
3.5 GB); `-M12G` is enough (about 25 minutes from a cold cache).

`src/CaTTExp/` contains core CaTT (syntax, typing, pasting contexts, a
certified checker), worked examples, and exploratory sketches under
`Sketch/`. Design findings from the sketches are in `notes/`.
