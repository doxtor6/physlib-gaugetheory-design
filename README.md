# Design notes for `GaugeTheory/` in Physlib

Notes on the structure of the `Physlib/ClassicalFieldTheory/GaugeTheory/` library:
the symbolic framework for the local content of a gauge theory (jets of fields,
gauge and Lorentz actions, invariants of a given mass dimension) that models such as
the Standard Model plug into.

The notes are written for discussion first and, later, as the basis of a paper.
Comments are welcome as issues or pull requests here, or on the Zulip thread of
[physlib PR #1415](https://github.com/leanprover-community/physlib/pull/1415).

## Contents

| file | what it is |
| --- | --- |
| [`notes/GaugeTheory-design.tex`](notes/GaugeTheory-design.tex), [`.pdf`](notes/GaugeTheory-design.pdf) | The intended five-layer structure of the library, the rules it follows, open questions, and the distance from the current tree. |

## Building

The notes use `fontspec` and need a Unicode-aware engine. With
[tectonic](https://tectonic-typesetting.github.io/):

```sh
make            # builds every notes/*.tex into notes/*.pdf
```

or `tectonic notes/GaugeTheory-design.tex` directly. XeLaTeX or LuaLaTeX also
work. The PDFs are committed so that nothing has to be built to read them. If GitHub's preview does not display one, use the raw file: [GaugeTheory-design.pdf](https://github.com/doxtor6/physlib-gaugetheory-design/raw/main/notes/GaugeTheory-design.pdf).

## License

The text is released under [CC BY 4.0](LICENSE).
