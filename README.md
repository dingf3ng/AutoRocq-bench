# AutoRocq-bench

AutoRocq-bench is a corpus of Rocq/Coq proof obligations extracted from real C code, intended for evaluating interactive or automated theorem proving workflows.

The benchmark targets **Rocq (formerly Coq) 8.18.0** and contains obligations derived from:

- **SV-COMP programs** (`svcomp`)
- **Linux-kernel modules** (`verker`)

At a high level, each benchmark entry consists of 
1. a `.v` file (with a *single* unproved theorem `wp_goal`), and 
2. an associated entry in `report.json` that points to its origin in the source code in `source_programs/`.

## What Is In This Repository

Key contents:

- `benchmarks/`
  - `svcomp/`: Benchmark directories.
  - `verker/`: Benchmark directories.
  - `svcomp-ablation.txt`: list of 70 sampled goals from `svcomp/`.
  - `svcomp-ablation.txt`: list of 571 remaining goals from `svcomp/`.
  - `verker-assert.txt`: list of 60 assertion goals from `verker/`.
- `source_programs/`
  - `svcomp/`: original C source files for `benchmarks/svcomp`.
  - `verker/`: original C headers/sources for `benchmarks/verker`.
- `libautorocq/`
  - Library for compiling Coq benchmark files.


## Citation / Attribution

If you use our work for academic research, please cite our paper:

```
@article{autorocq,
  title={Agentic Verification of Software Systems},
  author={Tu, Haoxin and Zhao, Huan and Song, Yahui and Zafar, Mehtab and Meng, Ruijie and Roychoudhury, Abhik},
  journal={Proceedings of the ACM on Software Engineering},
  volume={1},
  number={FSE},
  year={2026},
  publisher={ACM New York, NY, USA}
}
```


