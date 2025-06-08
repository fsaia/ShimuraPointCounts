// load "point_counts_all_traces.m"; // version that loads large list of data on forms
load "point_counts_10k.m"; // version that load smaller list of data on forms
load "quot_genus.m";

start_time := Cputime();

// HallDivisors : given positive integer N, returns sequence of all Hall Divisors d || N. 
HallDivisors := function(N)
    assert N ge 1;
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1];
end function;


// no_involutions: uses a crtierion of Gonzalez (Equation 2.2 in "Constaints on the automorphism
// group of a curve", 2017) to check if X_0^D(N)^* = X_0^D(N)/W_0(D,N) could have an involution
// using point counts over the finite fields F_{2^i}. Outputs "true" if this curve
// provably has no involutions. The output "false" gives no information. 
// The parameter m determines the largest cardinality 2^m finite field used in the check.

// Note: currently restricted to the case N=1, D = p*q (I'm not sure of the syntax to get the 
// point count specifically for the full quotient otherwise). 

no_involutions := function(D,N,imax)

    assert D*N mod 2 eq 1;
    star_gens := [{i} : i in [1..#PrimeDivisors(D*N)]];

    counts, g_star := shirec(2,D,N,star_gens : m := imax);
    assert g_star ge 2;
    sum_upper_bound := 2*g_star+2; 

    Ai_list := []; // initializing list, to contain counts |A_i| for i odd, 1 <= i <= imax

    for i in [i : i in [1..imax] | i mod 2 eq 1] do
        Ai := counts[i]; // number of points over F_{q^i}
        for j in [j : j in Divisors(i) | j lt i]  do
            Ai := Ai-Ai_list[Integers()!((j+1)/2)]; // subtracting from Ai as needed to get number of points over F_{q^i}
                                      // which don't live over F_{q^j} for some j<i. 
        end for;
        Append(~Ai_list,Ai); 
    end for; 

    sum := 0;

    for k in [k : k in [1..#Ai_list] | Ai_list[k] mod 2 eq 1] do
        sum := sum + (2*k-1);  // getting left-hand side of Gonzalez's Equation 2.2, summing up to n=imax. 
    end for; 

    if sum gt sum_upper_bound then
        return true;
    else
        return false; 
    end if;

end function;


// all_atkin_lehner_KR : uses results from Kontogeorgis--Rotger Theorems 1.6, 1.7
// to prove that Aut(X_0^D(N)) = W_0(D,N) in the case of N squarefree.
all_atkin_lehner_KR := function(D,N)

    assert IsSquarefree(N); 

    F_D := Factorization(D);
    F_N := Factorization(N);
    g := Integers()!genus(D,N);
    r := #F_D + #F_N; // r = omega(DN)
    e_1 := e1_from_facts(F_D,F_N,N);
    e_3 := e3_from_facts(F_D,F_N,N);

    if (D*N mod 3) eq 0 then // using KR Thm 1.7 (i) with m=3
        
        check_3 := true; // check on prime divisors of N

        for factor in F_N do
            p := factor[1];
            if (KroneckerSymbol(-3,p) eq -1) then
                check_3 := false;
                break;
            end if;
        end for;

        if check_3 eq true then // then we check factors of D
            c := 0;
            for factor in F_D do
                p := factor[1];
                if (KroneckerSymbol(-3,p) eq 1) then
                    c := c+1;
                    if c gt 1 then 
                        break;
                    end if;
                end if; 
            end for; 

            if (c le 1) then 
                return true;
            end if;
        end if;
    end if; 


    // if previous check didn't succeed, try KR Thm 1.6 i and 1.6 ii and Lemma arguments
    if (((e_1 eq 0) and (e_3 eq 0))) or (r eq Valuation(g-1,2)+2)  then
        return true;
    end if; 

    // if previous checks didn't succeed, try KR Thm 1.7 (iii) with point counts over
    // F_{p} for p prime up to 100 not dividing 2*D*N
    for p in [p : p in PrimesUpTo(100) | (p ne 2) and (not ((p in [pair[1] : pair in F_D]) or (p in [pair[1] : pair in F_N])))] do // odd primes up to 100 of good red'n for X_0^D(N)
            if r eq Valuation(shiALpoints(p,1,D,N,[]),2)+1 then 
                return true;
            end if; 
    end for;

    // If none of the above methods succeeded, we return false
    return false;
end function; 


// all_atkin_lehner_KR_no_point_counts : uses results from Kontogeorgis--Rotger Theorems 1.6, 1.7
// to prove that Aut(X_0^D(N)) = W_0(D,N) in the case of N squarefree.
all_atkin_lehner_KR_no_point_counts := function(D,N)

    assert IsSquarefree(N); 

    F_D := Factorization(D);
    F_N := Factorization(N);
    g := Integers()!genus(D,N);
    r := #F_D + #F_N; // r = omega(DN)
    e_1 := e1_from_facts(F_D,F_N,N);
    e_3 := e3_from_facts(F_D,F_N,N);

    if (D*N mod 3) eq 0 then // using KR Thm 1.7 (i) with m=3
        
        check_3 := true; // check on prime divisors of N

        for factor in F_N do
            p := factor[1];
            if (KroneckerSymbol(-3,p) eq -1) then
                check_3 := false;
                break;
            end if;
        end for;

        if check_3 eq true then // then we check factors of D
            c := 0;
            for factor in F_D do
                p := factor[1];
                if (KroneckerSymbol(-3,p) eq 1) then
                    c := c+1;
                    if c gt 1 then 
                        break;
                    end if;
                end if; 
            end for; 

            if (c le 1) then 
                return true;
            end if;
        end if;
    end if; 


    // if previous check didn't succeed, try KR Thm 1.6 i and 1.6 ii and Lemma arguments
    if (((e_1 eq 0) and (e_3 eq 0))) or (r eq Valuation(g-1,2)+2)  then
        return true;
    end if; 

    // If none of the above methods succeeded, we return false
    return false;
end function; 




    // no_involution_star_pairs := [];

    // level_bound := 10000; 

    // // List of odd imaginary quadratic discriminants D>1 up to level_bound 

    // pairs_up_to_bound := [];

    // D_list := [D : D in [6..level_bound] | (MoebiusMu(D) eq 1) and (D mod 2 eq 1)];

    // for D in D_list do 

    //     // N squarefree, odd, and coprime to D such that D*N <= level_bound and g(X_0^D(N)) ge 2)
    //     N_list := [N : N in [1..Floor(level_bound/D)] | ((IsSquarefree(N)) and (GCD(D,N) eq 1)) and (N mod 2 eq 1)];

    //     for N in [N : N in N_list | quot_genus(D,N,HallDivisors(D*N)) ge 2] do
    //         Append(~pairs_up_to_bound,[D,N]);
    //     end for;

    // end for;

    // for pair in pairs_up_to_bound do
    //     print pair;
    //     if no_involutions(pair[1],pair[2],50) then
    //         Append(~no_involution_star_pairs,pair);
    //     end if;
    // end for;
    

// we know with the hypotheses on the pairs (D,N) in no_involution_star_pairs that 
// Aut(X_0^D(N)) = W_0(D,N)
    // all_atkin_lehner := no_involution_star_pairs;


// we next check pairs remaining in pairs_up_to_bound using results
// from Kontogeorgis--Rotger 2008
    // for pair in [pair : pair in pairs_up_to_bound | not (pair in all_atkin_lehner)] do
    //     D := pair[1];  
    //     print D; // progress tracker
    //     N := pair[2];
    //     if all_atkin_lehner_KR(D,N) eq true then
    //         Append(~all_atkin_lehner, pair); 
    //     end if;
    // end for; 

    // Sort(~all_atkin_lehner);

    // end_time := Cputime();



// SetOutputFile("no_involution_star_pairs_10k.m");
// print "no_involution_star_pairs_10k := ", no_involution_star_pairs, ";";
// UnsetOutputFile();

// SetOutputFile("all_atkin_lehner_10k.m");
// print "// Time taken", end_time - start_time;
// print "all_atkin_lehner_10k := ", all_atkin_lehner, ";";
// UnsetOutputFile();

// SetOutputFile("unknown_aut_pairs_10k.m");
// print "unknown_aut_pairs_10k := ", [pair : pair in pairs_up_to_bound | not (pair in all_atkin_lehner)], ";";
// UnsetOutputFile();


