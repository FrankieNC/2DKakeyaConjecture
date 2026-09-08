# Towards a Formalisation of the Kakeya Conjecture in $\mathbb{R}^2$
[![Build](https://github.com/FrankieNC/2DKakeyaConjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/FrankieNC/2DKakeyaConjecture/actions/workflows/lean_action_ci.yml)

This repository contains the work for my MSc thesis in Pure Mathematics, undertaken at Imperial College London during the 2024–2025 academic year under the supervision of Dr Bhavik Mehta ([@b-mehta](https://github.com/b-mehta)).

The central aim of this project is the formalisation of the Kakeya conjecture in the plane within the Lean theorem prover. The two-dimensional case was resolved by [Davies (1971)](https://doi.org/10.1017/S0305004100046867) [1], who proved that every Besicovitch set in $\mathbb{R}^2$ has full Hausdorff dimension. The three-dimensional case remained open until it was recently resolved by [Wang and Zahl (2025)](https://arxiv.org/abs/2502.17655) [2]. This project's main focus was formalising the existence of a Besicovitch set in $\mathbb{R}^2$.

This repository contains the Lean formalisation code, along with the associated thesis, which you can read [here](https://github.com/FrankieNC/2DKakeyaConjecture/blob/main/docs/CHOTUCK_FRANCESCO_01925507.pdf).

> **MSc submission snapshot:** the version of the code submitted for assessment is tagged [`v1.0.0-msc-submission`](https://github.com/FrankieNC/2DKakeyaConjecture/releases/tag/v1.0.0-msc-submission).

I plan to continue developing this project with regular updates. Contributions are welcome via PRs — contribution guidelines may follow at some point.

## References

[1] R. O. Davies, ["Some remarks on the Kakeya problem,"](https://doi.org/10.1017/S0305004100046867) *Math. Proc. Cambridge Philos. Soc.*, 69 (1971), 417–421.

[2] H. Wang and J. Zahl, ["Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions,"](https://arxiv.org/abs/2502.17655) arXiv:2502.17655 (2025).
