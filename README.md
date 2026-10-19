# Supplementary material: "Gaps between roots in ballistic deposition on a strip"

## Lean 4 (`lean/`)
Plain Lean 4 v4.12.0 (no Mathlib). Compile each file with `lean FILE.lean`.
There is no `sorry`; `#print axioms` shows only propext, Quot.sound and Classical.choice.
- `Deposition.lean`: Lemma 2.1, the root criterion (`BD.isRoot_iff`, `BD.cyc_isRoot_iff`).
- `LocalMinima.lean`: Lemma 2.3 in full (`LM.not_isMin_succ`, `LM.gap_product_zero`); the locality of Y_j; no valley strictly inside a gap; the block patterns used in Proposition 5.3 (`LM.GoodS.*`).
- `Deposition.lean` also contains the comparison step of Proposition 7.4 (`BD.run_shift_ge`, `BD.run_shift_le`, `BD.run_restart_bounds`).

## Computations (`code/`)
Needs Python 3 with sympy (and scipy for one check) and a C compiler.
- `constants.py`: exact a_i, u_i, v_i, b_i by counting up/down words (Table 1).
- `closed_a.py`, `closed_b.py`, `check_cf.py`, `task34_numbers.py`: symbolic derivation of Theorems 4.3 and 4.5 and exact checks for i ≤ 30; the constants in Corollary 4.6 and Theorem 6.1.
- `cyc_enum.c` + `cyc_check.py`, `cyc_enum2.c` + `cross_check.py`: exhaustive enumeration of circular arrangements, K ≤ 13 (Proposition 3.1, Remark 3.2). Build with `gcc -O2 -o cyc_enum cyc_enum.c`, then run `./cyc_enum K > cyc_out.txt` and `./cyc_enum2 K > cross_K.txt` for each K.
- `checks_task1.py`: deposition simulation versus Lemma 2.1, and the block patterns.
- `check_integral_rep.py`, `sigma_table.py`: the integral representations of u_ij, v_ij; the generating function; the Σ table.
- `bracket.c`: exact E max H_n over all K^n words (the bracket 3 ≤ 4v_4 ≤ 3.2097).

## Figures (`figures/`)
- `make_fig1.py`: generates `fig_reduction.tex` (TikZ; compile with pdflatex). It uses the seeded example (K = 12, seed 113) and asserts that the roots equal the valleys.
- `speed.c`, `speed_data.txt`, `make_fig2.py`: Monte Carlo data for Figure 2 (4 runs per K, 10^5 deposits per site; build with `gcc -O2 -o speed speed.c` and run `./speed K steps 1 seed`) and the plotting script (matplotlib, pgf backend with pdflatex).
