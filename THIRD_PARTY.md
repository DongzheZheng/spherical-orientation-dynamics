# Third-party dependencies

The release distributes original project sources and generated data/figures. Dependency source trees, binaries and caches are excluded.

| Dependency | Pinned source or tested release | License |
| --- | --- | --- |
| Lean | 4.29.0 and 4.33.1 | [Apache-2.0](https://github.com/leanprover/lean4/blob/master/LICENSE) |
| mathlib, main project | `8a178386ffc0f5fef0b77738bb5449d50efeea95` | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/8a178386ffc0f5fef0b77738bb5449d50efeea95/LICENSE) |
| mathlib, sphere project | `0df444a360eaa60ab8c11dca51a86af692955474` | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/LICENSE) |
| DifferentialGeometry | `7a48598d35109aa99d1cc678e2724c213cdf4ff3` | [Apache-2.0 license](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/LICENSE), [NOTICE](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/NOTICE) |
| NumPy | 2.4.3 | [BSD-3-Clause](https://numpy.org/doc/stable/license.html) |
| Matplotlib | 3.10.8 | [Matplotlib license](https://matplotlib.org/stable/project/license.html) |
| pypdf | 6.10.0 for figure metadata processing | [BSD-3-Clause](https://pypdf.readthedocs.io/en/stable/meta/LICENSE.html) |

The Lean lock files also record transitive package revisions. Standard TeX packages are needed only to rebuild the standalone plot sources.
