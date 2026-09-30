# Numerical and figure reproduction evidence

`suite_validation_portable.json` records all five successful default-resolution experiments, interpreter/library versions and elapsed times. `reference_comparison.json` checks the twenty reference CSVs and five canonical validation reports. All checked numerical values reproduced exactly in this run.

`figure_validation.json` records the twelve successfully generated English PDFs. Ten use the standalone TeX sources and regenerated numerical tables; two are Python-generated 3D visualizations. The reference PDF files have empty document metadata and no XMP metadata. Rendered pages were reviewed for legibility and layout.

`runner_validation.json` records a separate successful execution of the public reproduction runner and reference comparator. These checks verify the reproducibility of the finite-resolution experiments, not continuum error bounds or the mathematical theorems.
