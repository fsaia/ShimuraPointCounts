# ShimuraPointCounts
This repository contains Magma code for the paper *Point counts, automorphisms, and gonalities of Shimura curves* by Pietro Mercuri, Oana Padurariu, Frederick Saia, and Claudio Stirpe ([arXiv:2507.15992](https://arxiv.org/abs/2507.15992)).


## Point Counts  

This directory contains the file for our main point count computations function, which is an implementation of Algorithm 1.1 in our paper (see also Section 4), as well as an examples file illustrating use of this function and files containing trace data that can be used for the main function.

- `counting_points.m`: Code for computing point counts on $X_0^D(N)$ and its Atkin--Lehner quotients over finite fields. This corresponds to Algorithm 1.1 in the paper. There are two ways to run the main function: you can either compute relevant Hecke trace data from scratch as part of the data using the included function, or can load in pre-computed data in the form specified for input for the main function. For computations in the files `aut_checks.m` and `tetragonal_sieving.m` which use the main `shipoints` function defined herein, in practice for speed we load in pre-computed trace data, modified from data obtained from the LMFDB, via the file `tracesALL.m`, which allows for roughly $DN < 10000$. We also include here the file `traces10k.m` which allows for levels $DN < 1433$ and is preferred in this level range as it takes up less memory. Alternatively, one can use the `prepare_forms` code in this file to compute the necessary input data from scratch at the sacrifice of speed.

- `examples.m`: This file contains examples displaying the use of the main point-counts function `shipoints` and the function `shiweil` for computing Weil polynomials defined in the file `counting_points.m`. 

- `traces10k.m`: Data of traces of action of Hecke operators for levels up to $1433$, modified from data available on the LMFDB. This file data may be used in the main function in `counting_points.m`.

- `tracesALL.m`: Data of traces of action of Hecke operators for levels up to $10000$, modified from data available on the LMFDB. This file data may be used in the main function in `counting_points.m`.


## Automorphisms

This directory contains code relevant to proving Theorem 1.3 in our paper (see also Section 5). To run all of these checks, one will need the files from the Point Counts directory as well as the auxiliary file `quot_genus.m`.

- `aut_checks.m`: Code with checks on the automorphism group of curves $X_0^D(N)$, and their Atkin--Lehner quotients, having genus $g>1$ and $D>1$. The main functions are `no_involutions.m`, which assumes $DN$ is even and uses point counts to attempt a sufficient check for $X_0^D(N)^*$ to have no involutions in its automorphism group, and `all_atkin_lehner_KR`, which assumes $N$ is squarefree and coprime to $D$ and uses point counts and results of Kontogeorgis--Rotger to prove that all non-trivial automorphisms of $X_0^D(N)$ are Atkin--Lehner involutions. This file requires `counting_points.m` if using these two main functions. Note that the full strength of our main theorem on Automorphism groups of $X_0^D(N)$ and its Atkin--Lehner quotients relies on loading in a large amount of pre-computed data on Hecke traces available on the LMFDB, which we include in this repository in a modified form as `tracesALL.m`.  

- `no_involution_star_pairs_10k.m`: List of all $9288$ of the $10609$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant over $\mathbb{Q}$, $N$ a positive integer which is squarefree and coprime to $D$, $g(X\_0^D(N)^\*) > 2$, and $DN < 10000$ for which we prove that $X_0^D(N)^\*$ has no non-trivial involutions using point counts with the result of González. Computed in `aut_checks.m`. This file is needed for `tetragonal_sieving.m`. 

- `unknown_aut_star_pairs_10k.m`: List of all $1321$ of the $10609$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant over $\mathbb{Q}$, $N$ a positive integer which is squarefree and coprime to $D$, $g(X\_0^D(N)^\*) > 2$, and $DN < 10000$ for which we do not determine in this work whether $X\_0^D(N)^\*$ has a non-trivial involution. Computed in `aut_checks.m`.  

- `all_atkin_lehner_10k.m`: List of all $10597$ of the $10609$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant over $\mathbb{Q}$, $N$ a positive integer which is squarefree and coprime to $D$, $g(X_0^D(N)^*) > 2$, and $DN < 10000$ for which we have proven that all automorphisms of $X_0^D(N)$ are Atkin--Lehner. Computed in `aut_checks.m`. This file is needed for `tetragonal_sieving.m`.

- `unknown_aut_pairs_10k.m`: List of all $12$ of the $10609$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant over $\mathbb{Q}$, $N$ a positive integer which is squarefree and coprime to $D$, $g(X_0^D(N)^*) > 2$, and $DN < 10000$ for which we do not determine in this work whether $X_0^D(N)$ has a non-Atkin--Lehner involution. Computed in `aut_checks.m`.  


## Tetragonals

This directory contains code relevant to proving Theorem 1.5 in our paper (see also Section 6). To run all of these checks, one will need the files from the Point Counts directory, the file `no_involution_star_pairs_10k.m` from the Automorphisms directory, and all files from the Auxiliary Files directory.

- `tetragonal_checks.m`: Initial code for narrowing candidates $X_0^D(N)$ for being geometrically tetragonal using genus computations and Abramovich's linear lower bound on the gonality of $X_0^D(N)$ in terms of its genus. This corresponds to the discussion between Lemma 6.14 and Proposition 6.15 in our paper.  

- `tetragonal_candidates.m`: List of all $516$ geometrically tetragonal candidate pairs computed in `tetragonal_checks.m`. This file is needed in `tetragonal_sieving.m`.  

- `tetragonal_sieving.m`: We use various information and techniques (including genus computations, known gonalities, Castelnuovo--Severi arguments, finite field point counts, checks on automorphism groups, and checks for rational CM points on Atkin--Lehner quotients) to narrow the tetragonal candidates listed in `tetragonal_candidates.m`, either by identifying them as tetragonal (over $\mathbb{Q}$ or geometrically) or proving they are not tetragonal (over $\mathbb{Q}$ or geometrically). This file accounts for the remainder of the proof of Theorem 1.5, with the majority of the code implementing the checks discussed in detail in Proposition 6.15. Note: For the point count checks using the `shipoints` function from `counting_points.m`, one must either load in a file containing pre-computed trace data for the `forms` input (currently loaded in as `traces10k.m` in this file) or must instead adjust the `shipoints` evaluations herein to compute the necessary data from scratch using the `prepare_forms` function in `counting_points.m`.  

- `remaining_geom_tetragonal_candidates.m`: All $32$ coprime pairs $(D,N)$ with $D>1$ for which we remain unsure of whether $X_0^D(N)$ is geometrically tetragonal. This list is computed in `tetragonal_sieving.m`.  

- `remaining_tetragonal_candidates.m`: All $32$ coprime pairs $(D,N)$ with $D>1$ for which we remain unsure of whether $X_0^D(N)$ is tetragonal over $\mathbb{Q}$. This list is computed in `tetragonal_sieving.m`.

- `geom_tetragonal_pairs.m`: List of all $161$ pairs $(D,N)$ for which we prove $X_0^D(N)$ is geometrically tetragonal. If $X_0^D(N)$ is geometrically tetragonal and is not in this list, then $(D,N)$ must be among the $32$ pairs listed in the file `remaining_geom_tetragonal_candidates.m`.

- `tetragonal_pairs.m`: List of all $141$ pairs $(D,N)$ for which we prove $X_0^D(N)$ is tetragonal over $\mathbb{Q}$. If $X_0^D(N)$ is tetragonal over $\mathbb{Q}$ and is not in this list, then $(D,N)$ must be among the $32$ pairs listed in the file `remaining_tetragonal_candidates.m`.


## Auxiliary Files

- `quot_genus.m`: Code for computing genera of Atkin--Lehner quotients of $X_0^D(N)$ assuming $D>1$. The calculation uses Riemann--Hurwitz along with counts of fixed points of Atkin--Lehner involutions from work of Ogg. This file is needed for `aut_checks.m`, `tetragonal_checks.m`, `tetragonal_sieving.m`, `AL_identifiers.m`

- `AL_identifiers.m`: Code for working with Atkin--Lehner subgroups of the automorphisms group of $X_0^D(N)$. In particular, this file contains code for going between lists of all elements of a subgroup and minimal length lists of generators, and for listing all subgroups of the Atkin--Lehner group $W_0(D,N)$. This file is needed for `tetragonal_checks.m` and `tetragonal_sieving.m`.

- `known_gonalities.m`: Known lists of coprime pairs $(D,N)$ with $D>1$ so that the curve $X_0^D(N)$ has genus $0$ or $1$ or has gonality over $\mathbb{Q}$ or geometric gonality at most 3. This file is needed for `tetragonal_checks.m` and `tetragonal_sieving.m`.

- `cond_disc_list_allO.m`: list of all (not just maximal) imaginary quadratic orders of class number up to $100$. The $i^\text{th}$ element is the complete list of sequences $[f,d_K] = [\text{conductor}, \text{fundamental disc}]$ for imaginary quadratic orders of class number $i$. Generated using list of maximal orders by M. Watkins. This list is used in least degree computations in `shimura_curve_CM_locus.m`, and hence is needed for `tetragonal_sieving.m`.

- `shimura_curve_CM_locus.m`: The aim of this code, from the paper *CM points on Shimura curves via QM-equivariant isogeny volcanoes* (Saia 2024), is to compute the $\Delta$-CM locus on $X_0^D(N)$ for any imaginary quadratic discriminant $\Delta$ and positive integer $N$ coprime to a given quaternion discriminant $D$. This is done via the QM-equivariant isogeny volcano approach of the referenced paper of Saia in the $D>1$ case, and of work of Clark--Saia in the $D=1$ case. In particular, this file contains code to enumerate all CM points of a specified discriminant $\Delta$ with all possible residue fields up to isomorphism for one of these Shimura curves. This is used in quadratic CM point computations in `tetragonal_sieving.m`.  


Shield: [![CC BY 4.0][cc-by-shield]][cc-by]

This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
[cc-by-shield]: https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg
