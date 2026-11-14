# SimpleSub (Lean)

Mechanized metatheory for the OCaml Simple-sub implementation in `../lib`.
See the "Mechanized metatheory" section of `../README.md` for what is
proved.

```sh
lake build
```

| File | Contents |
|---|---|
| `SimpleSub/Syntax.lean` | term syntax (mirrors `lib/syntax.ml`) |
| `SimpleSub/Types.lean` | types with rows, locally nameless μ, closedness, contractiveness, unguarded size |
| `SimpleSub/Sub.lean` | guarded coinductive subtyping, rows compared as label maps; reflexivity, transitivity (cut elimination), S-Rec, the paper's §5.1.3 example, row examples, non-contractive counterexample |
| `SimpleSub/Rows.lean` | row algebra; exactness of the row rewrites in `lib/simplify.ml` and `lib/subsume.ml` |
