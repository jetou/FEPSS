## Finding and exploring promising search space for The 0–1 Multidimensional Knapsack Problem (FEPSS)

 This repository contains the code used for the experiments in the paper "Finding and exploring promising search space for The 0–1 Multidimensional Knapsack Problem". (https://authors.elsevier.com/c/1jQFp5aecSvMEl)

 The 0–1, Multidimensional Knapsack Problem (MKP) is a classical NP-hard combinatorial optimization problem with many engineering applications. In this paper, we propose a novel algorithm combining evolutionary computation with the exact algorithm to solve the 0–1 MKP. It maintains a set of solutions and utilizes the information from the population to extract good partial assignments. To find high-quality solutions, an exact algorithm is applied to explore the promising search space specified by the good partial assignments. The new solutions are used to update the population. Thus, the good partial assignments evolve towards a better direction with the improvement of the population. Extensive experimentation with commonly used benchmark sets shows that our algorithm outperforms the state-of-the-art heuristic algorithms, TPTEA and DQPSO, as well as the commercial solver CPlex. It finds better solutions than the existing algorithms and provides new lower bounds for 10 large and hard instances.



### Requirements

- `C++ == 14`
- `CMake == 3.3.2`
- `CPlex == 20.1`


### Quick Start

    <C++ compiled file> <total algorithm runtime> <CPLEX single run time> <seed number> <benchmark type> <mkp problem instance> <output dir>
    
- `<C++ compiled file>`: the executable file generated from your C++ code.
- `<total algorithm runtime>`: the total time for the algorithm to run.
- `<CPLEX single run time>`: the time for a single run of CPLEX.
- `<seed number>`: the seed number for randomization.
- `<benchmark type>`: should be either `1` for Orlibrary or `2` for MK_GK.
- `<mkp problem instance>`: the specific problem instance for MKP.
- `<output dir>`: the directory where the output will be stored.

Example:

    ./FEPSS 7200 10 1 1 ../benchmark/30.500/30.500.0.txt ./ResultsAblation/ReRunOri/Result_0.txt 

### Citation

    @article{XU2024111934,
    title = {Finding and exploring promising search space for The 0–1 Multidimensional Knapsack Problem},
    journal = {Applied Soft Computing},
    volume = {164},
    pages = {111934},
    year = {2024},
    issn = {1568-4946},
    doi = {https://doi.org/10.1016/j.asoc.2024.111934},
    url = {https://www.sciencedirect.com/science/article/pii/S1568494624007087},
    author = {Jitao Xu and Hongbo Li and Minghao Yin},
    }