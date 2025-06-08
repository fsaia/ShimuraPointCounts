# ShimuraPointCounts
Magma code for the paper "Point counts of Shimura curves over finite fields" by Pietro Mercuri, Oana Padurariu, Frederick Saia, and Claudio Stirpe

## Main Files

- `aut_checks.m`: Code with checks on the automorphism group of curves $X_0^D(N)$, and their Atkin--Lehner quotients, having genus $g>1$ and $D>1$. The main functions are `no_involutions.m`, which assumes $DN$ is even and uses point coints to attempt a sufficient check for $X_0^D(N)^*$ to have no involutions in its automorphism group, and `all_atkin_lehner_KR`, which assumes $N$ is squarefree and coprime to $D$ and uses point counts and results of Kontogeorgis--Rotger to prove that all non-trivial automorphisms of $X_0^D(N)$ are Atkin--Lehner involutions. This file requires either `point_counts_10k.m` or `point_counts_all_traces.m` if using these two main functions, and one can change which file is loaded in by commenting and uncommenting the relevant lines at the beginning.

- `tetragonal_checks.m`: Initial code for narrowing candidates $X_0^D(N)$ for being geometrically tetragonal using genus computations and Abramovich's linear lower bound on the gonality of $X_0^D(N)$ in terms of its genus.
  
- `tetragonal_sieving.m`: We use various information and techniques (including genus computations, known gonalities, Castelnuovo--Severi arguments, finite field point counts, checks on automorphism groups, and checks for rational CM points on Atkin--Lehner quotients) to narrow the tetragonal candidates listed in `tetragonal_candidates.m`, either by identifying them as tetragonal (over $\mathbb{Q}$ or geometrically) or proving they are not tetragonal (over $\mathbb{Q}$ or geometrically). 


## Required Files

- `quot_genus.m`: Code for computing genera of Atkin--Lehner quotients of $X_0^D(N)$ assuming $D>1$. The calculation uses Riemann--Hurwitz along with counts of fixed points of Atkin--Lehner involutions from work of Ogg. This file is needed for `aut_checks.m`, `tetragonal_checks.m`, `tetragonal_sieving.m`, `AL_identifiers.m`

- `AL_identifiers.m`: Code for working with Atkin--Lehner subgroups of the automorphisms group of $X_0^D(N)$. In particular, this file contains code for going between lists of all elements of a subgroup and minimal length lists of generators, and for listing all subgroups of the Atkin--Lehner group $W_0(D,N)$. This file is needed for `tetragonal_checks.m` and `tetragonal_sieving.m`.

- `traces10k.m`: Data of traces of action of Hecke operators for levels up to $10000$ from the LMFDB. This file is needed for `point_counts_10k.m`, and so either this file or `tracesALL.m` is needed for `aut_checks.m`.

- `point_counts_10k.m`: Code for computing point counts on $X_0^D(N)$ and its Atkin--Lehner quotients over finite fields. This version loads in trace data from `traces10k.m`, and allows for roughly $DN < 14000$. This file is needed for `tetragonal_sieving.m`, and this file or `point_counts_all_traces.m` is needed for `aut_checks.m`. 

-  `point_counts_all_traces.m`: Code for computing point counts on $X_0^D(N)$ and its Atkin--Lehner quotients over finite fields. This version loads in trace data from `traces_ALL.m`, and allows for roughly $DN < 10000$. This file or `point_counts_10k.m` is needed for `aut_checks.m` (and specifically this version is needed for our main theorem on automorphism groups of $X_0^D(N)$ and its Atkin--Lehner quotients). 

-  `known_gonalities.m`: Known lists of coprime pairs $(D,N)$ with $D>1$ so that the curve $X_0^D(N)$ has genus $0$ or $1$ or has gonality over $\mathbb{Q}$ or geometric gonality at most 3. This file is needed for `tetragonal_checks.m` and `tetragonal_sieving.m`.

- `cond_disc_list_allO.m`: list of all (not just maximal) imaginary quadratic orders of class number up to $100$. The $i^\text{th}$ element is the complete list of sequences $[f,d_K] = [\text{conductor}, \text{fundamental disc}]$ for imaginary quadratic orders of class number $i$. Generated using list of maximal orders by M. Watkins. This list is used in least degree computations in `shimura_curve_CM_locus.m`, and hence is needed for `tetragonal_sieving.m`.

- `shimura_curve_CM_locus.m`: The aim of this code, from the paper *CM points on Shimura curves via QM-equivariant isogeny volcanoes* (Saia 2024)  is to compute the $\Delta$-CM locus on $X_0^D(N)$ for any imaginary quadratic discriminant $\Delta$ and positive integer $N$ coprime to a given quaternion discriminant $D$. This is done via the QM-equivariant isogeny volcano approach of the referenced paper of Saia in the $D>1$ case, and of work of Clark--Saia in the $D=1$ case. In particular, this file contains code to enumerate all CM points of a specified discriminant $\Delta$ with all possible residue fields up to isomorphism for one of these Shimura curves. This is used in quadratic CM point computations in `tetragonal_sieving.m`.


## Computed Lists

- `no_involution_star_pairs_10k.m`: List of all $4378$ of the $4830$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant over $\mathbb{Q}$, $N$ a positive integer which is squarefree and coprime to $D$, $DN$ odd, and $DN < 10000$ for which we prove that $X_0^D(N)^*$ has no non-trivial involutions using just point counts with the result of González (and not using additional results from Kontogeorgis--Rotger). Computed in `aut_checks.m`.
  
- `all_atkin_lehner_10k.m`: List of all $4718$ of the $4830$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant over $\mathbb{Q}$, $N$ a positive integer which is squarefree and coprime to $D$, $DN$ odd, and $DN < 10000$ for which we have proven that all automorphisms of $X_0^D(N)/W$ are Atkin--Lehner for each $W \leq W_0(D,N)$. Computed in `aut_checks.m`. This file is needed for `tetragonal_sieving.m`.

- `unknown_aut_pairs_10k.m`: List of all $112$ of the $4830$ pairs $(D,N)$ with $D>1$ an indefinite quaternion discriminant, $N$ a positive integer which is squarefree and coprime to $D$, $DN$ odd, and $DN < 10000$ for which we have not yet determined whether $X_0^D(N)^*$ has a non-trivial involution. Computed in `aut_checks.m`.

- `tetragonal_candidates.m`: List of all $516$ geometrically tetragonal candidate pairs computed in `tetragonal_checks.m`. This file is needed in `tetragonal_sieving.m`.

- `remaining_geom_tetragonal_candidates.m`: All $10$ coprime pairs $(D,N)$ with $D>1$ for which we remain unsure of whether $X_0^D(N)$ is geometrically tetragonal. This list is computed in `tetragonal_sieving.m`. 

- `remaining_tetragonal_candidates.m`: All $29$ coprime pairs $(D,N)$ with $D>1$ for which we remain unsure of whether $X_0^D(N)$ is tetragonal over $\mathbb{Q}$. This list is computed in `tetragonal_sieving.m`. 
